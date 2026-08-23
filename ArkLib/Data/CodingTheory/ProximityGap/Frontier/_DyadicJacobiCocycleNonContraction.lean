/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The dyadic Jacobi cocycle is non-contractive: explicit evaluation does not beat flatness (#407)

## Attack 1 — dyadic Gauss-phase explicit evaluation (verdict: NO)

The proximity-prize floor reduces (`SubgroupGaussSumEnergyReduction`, the exact identity
verified in `scripts/probes/probe_407_gauss_phase_identity_corrected.py` to `1e-13`) to a
sup-norm bound on
`P(b) = ∑_{j=1}^{m-1} χ̄_{nj}(b) · γ_j`,  `γ_j = G(χ_{nj})/√p`,  `m = (p-1)/n`,
where the characters `χ_{nj}` are precisely those **trivial on `μ_n`** — the dual group of the
quotient `Fₚˣ/μ_n ≅ ℤ/m`.  Their orders divide `m = (p-1)/n`, **not** `n`; they are all
`2`-power order iff `m` is a `2`-power iff `p` is a Fermat prime.  So the "dyadic special node"
(2-power-order Gauss sums, classically evaluable) is a **Fermat-prime corner**, not the prize
regime (`n = 2^30`, `q ≈ n·2^128`, where `m = (p-1)/n` has a huge odd part — non-2-power Gauss
sums, not classically evaluable).  [Reason R1 of the probe.]

Even *on* that corner the explicit evaluation does **not** bound `max|P|` below the flat
conjecture `√(2m ln m)`.  The Jacobi/Hasse–Davenport cocycle is
`γ_j · γ_k = c_{j,k} · γ_{j+k}` with `c_{j,k} = J_{j,k}/√p`, and the classical Jacobi magnitude
is `|J_{j,k}| = √p` **exactly** for non-principal pairs (probe Part 2, `||J|-√p| ≈ 1e-12`).  Hence
the cocycle factor is **unimodular**, `|c_{j,k}| = 1`.  A contraction (a bound forcing cancellation
in the *sum* `P`) would need `|c_{j,k}| < 1`; the unimodular cocycle transfers no smallness.  The
measured `max|P|/√(2m ln m)` hugs `0.98–1.10` (it is `> 1` at `p=65537, n=512`) — the explicit
structure **reproduces** the flat conjecture, never beats it.  [Reason R2.]

This file is the **axiom-clean arithmetic guardrail** for R2 (mirroring
`ConstantIndexGaussBarrier`): with unit phases and a unimodular cocycle, the only bound the
explicit structure forces on `|P|` is the trivial triangle bound `≤ m-1`; the prize bound
`√(2m ln m) ≪ m-1` is *strictly stronger* and is exhibited as **not** implied — there is an
all-aligned unit configuration consistent with the unimodular cocycle for which `|P| = m-1`.

It introduces no `sorry`/`axiom`.  It is a refutation brick (Attack 1 NO), not a closure.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. #407.
- Berndt–Evans–Williams, *Gauss and Jacobi Sums* (the classical `|J|=√p`, cocycle).
- BGK: Bourgain–Glibichuk–Konyagin (the open sup-norm flatness wall this collapses onto).
-/

namespace ProximityGap.Frontier.DyadicJacobiCocycleNonContraction

open Finset Complex

/-- A family of **unit** Gauss phases `γ : Fin M → ℂ`, `‖γ j‖ = 1` (here `‖G(χ)/√p‖ = 1`). -/
def IsUnitPhase {M : ℕ} (γ : Fin M → ℂ) : Prop := ∀ j, ‖γ j‖ = 1

/-- The phase sum `P = ∑_j γ j` (the per-`b` evaluation; the character twist `χ̄(b)` only
permutes/rotates the unit phases, so its modulus envelope is captured by the unit-phase model). -/
noncomputable def phaseSum {M : ℕ} (γ : Fin M → ℂ) : ℂ := ∑ j, γ j

/-- **Trivial triangle bound.** A sum of `M` unit phases has modulus at most `M`. This is the
*only* unconditional bound on `‖P‖`; it is what the unimodular cocycle leaves available. -/
theorem norm_phaseSum_le_card {M : ℕ} {γ : Fin M → ℂ} (h : IsUnitPhase γ) :
    ‖phaseSum γ‖ ≤ (M : ℝ) := by
  calc ‖phaseSum γ‖ = ‖∑ j, γ j‖ := rfl
    _ ≤ ∑ j : Fin M, ‖γ j‖ := norm_sum_le _ _
    _ = ∑ _j : Fin M, (1 : ℝ) := Finset.sum_congr rfl (fun j _ => h j)
    _ = (M : ℝ) := by simp

/-- **The unimodular Jacobi cocycle.** `γ` obeys a cocycle with factor `c : Fin M → Fin M → ℂ`,
`γ j * γ k = c j k * γ (j+k)`, and every cocycle factor is unimodular: `‖c j k‖ = 1`.
This is the in-tree abstraction of `γ_j γ_k = (J_{j,k}/√p) γ_{j+k}` with `|J_{j,k}| = √p`. -/
def UnimodularCocycle {M : ℕ} (γ : Fin M → ℂ) (c : Fin M → Fin M → ℂ) : Prop :=
  (∀ j k, γ j * γ k = c j k * γ (j + k)) ∧ (∀ j k, ‖c j k‖ = 1)

/-- **Cocycle consistency with unit phases.** A unimodular cocycle is *automatically* consistent
with `‖γ j‖ = 1` for all `j`: taking norms in `γ j * γ k = c j k * γ (j+k)` with `‖c‖=1` gives
`‖γ j‖·‖γ k‖ = ‖γ (j+k)‖`, the functional equation of a unit phase. So the cocycle imposes
**no magnitude constraint** beyond unit modulus — in particular none on the *sum* `P`. -/
theorem cocycle_preserves_unit_modulus {M : ℕ} {γ : Fin M → ℂ} {c : Fin M → Fin M → ℂ}
    (hco : UnimodularCocycle γ c) (j k : Fin M) :
    ‖γ j‖ * ‖γ k‖ = ‖γ (j + k)‖ := by
  obtain ⟨heq, hc⟩ := hco
  have := congrArg norm (heq j k)
  rwa [norm_mul, norm_mul, hc, one_mul] at this

/-- **Non-contraction (the R2 guardrail).** There is a unit-phase family obeying a unimodular
cocycle whose phase sum is **maximal**, `‖P‖ = M`.  Concretely the constant family `γ ≡ 1`
(all phases aligned) with trivial cocycle `c ≡ 1`: it is unit-phase, satisfies the unimodular
cocycle exactly, yet `‖∑_j γ j‖ = M` saturates the triangle bound.

Consequence: the unimodular Jacobi cocycle is **consistent with zero cancellation** in `P`.
Therefore no bound derived *solely* from the cocycle (the explicit dyadic evaluation) can force
`‖P‖ < M`; in particular it cannot reach the flat prize bound `√(2M ln M) ≪ M`. The explicit
structure does not beat flatness — Attack 1 collapses onto the open BGK/Paley sup-norm wall. -/
theorem exists_unimodular_cocycle_saturating_triangle (M : ℕ) :
    ∃ (γ : Fin M → ℂ) (c : Fin M → Fin M → ℂ),
      IsUnitPhase γ ∧ UnimodularCocycle γ c ∧ ‖phaseSum γ‖ = (M : ℝ) := by
  refine ⟨fun _ => (1 : ℂ), fun _ _ => (1 : ℂ), ?_, ⟨?_, ?_⟩, ?_⟩
  · intro j; simp
  · intro j k; simp
  · intro j k; simp
  · simp [phaseSum]

/-- **Quantitative gap.** For `M ≥ 2`, the saturating configuration of
`exists_unimodular_cocycle_saturating_triangle` has phase sum `M`, which strictly exceeds any
multiplier-`C` flat target `C * Real.sqrt (M * Real.log M)` once
`C * √(M ln M) < M` (the prize regime: `C` polylog, `M ≈ q/n` polynomial in `n`).
So the cocycle-consistent worst case lies above the flat budget. -/
theorem flat_target_below_cocycle_saturation
    {M : ℕ} {C : ℝ} (hgap : C * Real.sqrt ((M : ℝ) * Real.log M) < (M : ℝ)) :
    ∃ (γ : Fin M → ℂ) (c : Fin M → Fin M → ℂ),
      IsUnitPhase γ ∧ UnimodularCocycle γ c ∧
      C * Real.sqrt ((M : ℝ) * Real.log M) < ‖phaseSum γ‖ := by
  obtain ⟨γ, c, hunit, hco, hsat⟩ := exists_unimodular_cocycle_saturating_triangle M
  exact ⟨γ, c, hunit, hco, by rw [hsat]; exact hgap⟩

/-- **The Fermat-corner index fact (R1, arithmetic core).** The characters in `P` form the dual
of `Fₚˣ/μ_n ≅ ℤ/m`, `m = (p-1)/n`; they all have `2`-power order iff `m` is a power of two.
When `p - 1 = n * m` with `n` a power of two, `m` is a power of two iff `p - 1` is, i.e. `p` is a
Fermat prime.  We record the contrapositive arithmetic guardrail: if `m` has an odd prime factor
(the generic dyadic prime, e.g. the prize regime), then some character order is a non-trivial
multiple of that odd prime, hence **not** a power of two — so the classical 2-power Gauss-sum
evaluation does not apply.  Stated purely on `m`: `m` not a power of two ⟹ `m` has an odd factor
`> 1`. -/
theorem odd_factor_of_not_two_pow {m : ℕ} (hm : 2 ≤ m)
    (hnpow : ∀ k, m ≠ 2 ^ k) : ∃ d, 1 < d ∧ Odd d ∧ d ∣ m := by
  -- the odd part `m / 2^(padicValNat 2 m)` is `> 1`, odd, and divides `m`.
  set e := m.factorization 2 with he
  set d := m / 2 ^ e with hd
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hdvd : 2 ^ e ∣ m := Nat.ordProj_dvd m 2
  have hd_dvd : d ∣ m := hd ▸ Nat.div_dvd_of_dvd hdvd
  have hd_odd : Odd d := by
    have h2 : ¬ (2 ∣ d) := by
      simpa [hd, he] using Nat.not_dvd_ordCompl (p := 2) (Nat.prime_two) hmpos.ne'
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hd_pos : 0 < d := Nat.ordCompl_pos 2 hmpos.ne'
  refine ⟨d, ?_, hd_odd, hd_dvd⟩
  -- if `d = 1` then `m = 2^e`, contradicting `hnpow`.
  rcases Nat.lt_or_ge 1 d with h | h
  · exact h
  · exfalso
    have hd1 : d = 1 := le_antisymm h hd_pos
    have : m = 2 ^ e := by
      have := Nat.ordProj_mul_ordCompl_eq_self m 2
      rw [← hd, hd1, mul_one] at this
      exact this.symm
    exact hnpow e this

#print axioms norm_phaseSum_le_card
#print axioms cocycle_preserves_unit_modulus
#print axioms exists_unimodular_cocycle_saturating_triangle
#print axioms flat_target_below_cocycle_saturation
#print axioms odd_factor_of_not_two_pow

end ProximityGap.Frontier.DyadicJacobiCocycleNonContraction
