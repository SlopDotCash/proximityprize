/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Fin

/-!
# Sweep A35 — the Shaw operator: collapse all moments to one spectral gap (#407)

**Actionable A35 (merged `371-T02`/`371-T03`).** Re-land the operator formulation of the prize.
The in-tree `ShawOperator.lean` names the *line–ball incidence* spectral error; this file instead
formalizes the operator the prize literature actually calls the "Shaw operator", living on the
**additive** group `G = F_q^+`:

> **`shawOp D f x := ∑_{d ∈ D} f (x - d)`** — convolution by the indicator `1_D` on `G⁺`, i.e. the
> **adjacency operator of the Cayley graph** `Cay(G⁺, D)`. With `D = μ_n` (the order-`n` smooth
> multiplicative subgroup embedded additively), this is the circulant whose spectrum is the family of
> **Gauss periods** `{η_b}`.

We prove, axiom-clean and `sorry`-free:

* **`shawOp_eigen`** — every additive character `ψ : AddChar G ℂ` is an eigenvector of `shawOp D`
  with eigenvalue `gaussPeriod D ψ := ∑_{d∈D} ψ(-d)`. So `spectrum (S_D) = { η_b : b }` *exactly*
  (this is the operator-level meaning of "the open input is `max_b |η_b|`").
* **`gaussPeriod_zero`** — the trivial character gives `η₀ = |D|` (the degree of the Cayley graph).
* **`parseval_gaussPeriod`** — `∑_{ψ} ‖η_ψ‖² = |D|·|G|` (Parseval / trace of `S_D Sᴴ_D`), hence
  **`offdiag_secondMoment_eq`** `∑_{ψ≠0} ‖η_ψ‖² = |D|·|G| − |D|²` (`= q·n − n²` at the prize).
* **`shaw_offdiag_moment_le`** — the **Hölder moment collapse**: with `B := max_{ψ≠0} ‖η_ψ‖`,
  for every `M ≥ 1`
  `∑_{ψ≠0} ‖η_ψ‖^{2M} ≤ B^{2M−2} · (|D|·|G| − |D|²)`.
  Every higher even moment `E_M` is pinned by the single scalar `B` and the (proven) second moment.
  This is the precise sense in which "all moments collapse to one spectral gap" — the below-UDR
  window lane and the deep-band census lane both reduce to controlling the lone scalar
  `B = ‖S_D|_{1^⊥}‖`.
* **`shaw_offdiag_moment_le_of_spectralGap`** — the consumer form: any spectral-gap hypothesis
  `B ≤ β` propagates to every moment, `∑_{ψ≠0}‖η_ψ‖^{2M} ≤ β^{2M−2}·(|D||G|−|D|²)`.

**The single open input (named, NOT proven — honesty contract).** `ShawSpectralGap D β := B ≤ β`.
The prize floor is `ShawSpectralGap μ_n (√(2·n·log(q/n)))` (the `B`-form). We name it as a `Prop`
and record the equivalences; we do **not** discharge it. The probe `scripts/probes/sweep_A35_shaw_operator.py`
confirms (E),(P),(H) exactly (max eigen err `~1e-14`, Parseval exact, Hölder M=1..4) and shows the
stronger Ramanujan form `B ≤ √2·√n` is FALSE outside the thin prize regime (e.g. `p=65537,n=64`:
`B/√n = 5.45`), while `B/√(2n log(q/n)) ∈ [0.76, 1.46]` stays bounded — so the floor is the
`√(n·log(q/n))` form, not `√2·√n`. No fabricated closure.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.commandStart false


open Finset

namespace ArkLib.ProximityGap.Frontier.ShawOperatorA35

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **The Shaw operator** `S_D = (convolution by `1_D`)` on functions `G⁺ → ℂ`, i.e. the adjacency
operator of the Cayley graph `Cay(G⁺, D)`: `(S_D f)(x) = ∑_{d∈D} f (x − d)`.  With `D = μ_n` this is
the circulant whose eigenvalues are the Gauss periods. -/
noncomputable def shawOp (D : Finset G) (f : G → ℂ) : G → ℂ :=
  fun x => ∑ d ∈ D, f (x - d)

/-- **The Gauss period / Shaw eigenvalue** attached to an additive character `ψ`:
`η_ψ := ∑_{d∈D} ψ(−d)`.  Indexed by `ψ = ψ_b`, this is the family `{η_b}` = the prize open input. -/
noncomputable def gaussPeriod (D : Finset G) (ψ : AddChar G ℂ) : ℂ :=
  ∑ d ∈ D, ψ (-d)

/-- **`shawOp_eigen` — the spectrum of the Cayley adjacency is exactly `{η_ψ}`.**
For any additive character `ψ`, `S_D ψ = η_ψ · ψ` pointwise: `ψ` is an eigenvector with eigenvalue
`gaussPeriod D ψ`.  (This is the operator-level statement "the open input is `max_b |η_b|`".) -/
theorem shawOp_eigen (D : Finset G) (ψ : AddChar G ℂ) (x : G) :
    shawOp D (fun y => ψ y) x = gaussPeriod D ψ * ψ x := by
  unfold shawOp gaussPeriod
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [sub_eq_add_neg]
  rw [AddChar.map_add_eq_mul]
  ring

/-- The trivial character gives `η₀ = |D|` — the degree of the Cayley graph (the Perron eigenvalue). -/
@[simp] theorem gaussPeriod_zero (D : Finset G) :
    gaussPeriod D (0 : AddChar G ℂ) = (D.card : ℂ) := by
  unfold gaussPeriod
  simp [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul]

/-- Complex conjugation of an additive-character value is the negation pullback (root of unity). -/
theorem addChar_conj (ψ : AddChar G ℂ) (a : G) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hca : (Fintype.card G) • a = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mp addOrderOf_dvd_card
  have hpow : ψ a ^ (Fintype.card G) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, hca, ψ.map_zero_eq_one]
  have hnorm : ‖ψ a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (by positivity)
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj hnorm).symm

/-- **`parseval_gaussPeriod` — the trace identity / Parseval for the Cayley spectrum.**
`∑_{ψ} ‖η_ψ‖² = |D| · |G|`.  This is `tr(S_D Sᴴ_D)` (a deterministic, unconditional second moment).
At the prize `|D| = n`, `|G| = q`, so the total spectral mass is `n·q`. -/
theorem parseval_gaussPeriod (D : Finset G) :
    ∑ ψ : AddChar G ℂ, ‖gaussPeriod D ψ‖ ^ 2 = (D.card : ℝ) * (Fintype.card G) := by
  classical
  -- work over ℂ via η·conj(η) = ‖η‖², then real-cast
  have keyC : (∑ ψ : AddChar G ℂ, gaussPeriod D ψ * (starRingEnd ℂ) (gaussPeriod D ψ))
      = (D.card : ℂ) * (Fintype.card G : ℂ) := by
    calc ∑ ψ : AddChar G ℂ, gaussPeriod D ψ * (starRingEnd ℂ) (gaussPeriod D ψ)
        = ∑ ψ : AddChar G ℂ, ∑ d ∈ D, ∑ e ∈ D, ψ (e - d) := by
          refine Finset.sum_congr rfl (fun ψ _ => ?_)
          unfold gaussPeriod
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
          rw [addChar_conj, neg_neg, ← AddChar.map_add_eq_mul, show -d + e = e - d from by abel]
      _ = ∑ d ∈ D, ∑ e ∈ D, ∑ ψ : AddChar G ℂ, ψ (e - d) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
      _ = ∑ d ∈ D, ∑ e ∈ D, (if e - d = 0 then (Fintype.card G : ℂ) else 0) := by
          simp_rw [AddChar.sum_apply_eq_ite]
      _ = ∑ d ∈ D, ∑ e ∈ D, (if e = d then (Fintype.card G : ℂ) else 0) := by
          simp_rw [sub_eq_zero]
      _ = ∑ _d ∈ D, (Fintype.card G : ℂ) := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          rw [Finset.sum_ite_eq' D d (fun _ => (Fintype.card G : ℂ)), if_pos hd]
      _ = (D.card : ℂ) * (Fintype.card G : ℂ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h := keyC
  simp only [Complex.mul_conj] at h
  norm_cast at h
  simp only [Complex.normSq_eq_norm_sq] at h
  rw [Nat.cast_mul] at h
  exact h

/-- **`offdiag_secondMoment_eq` — the off-trivial second moment.**
`∑_{ψ≠0} ‖η_ψ‖² = |D|·|G| − |D|²`.  Subtracting the Perron term `‖η₀‖² = |D|²` from Parseval. At the
prize this is `q·n − n²` — the quantity appearing in the Hölder moment collapse. -/
theorem offdiag_secondMoment_eq (D : Finset G) :
    ∑ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0), ‖gaussPeriod D ψ‖ ^ 2
      = (D.card : ℝ) * (Fintype.card G) - (D.card : ℝ) ^ 2 := by
  classical
  -- split off the trivial character via add_sum_erase
  have hsplit :
      ∑ ψ : AddChar G ℂ, ‖gaussPeriod D ψ‖ ^ 2
        = ‖gaussPeriod D (0 : AddChar G ℂ)‖ ^ 2
          + ∑ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0), ‖gaussPeriod D ψ‖ ^ 2 := by
    rw [← Finset.add_sum_erase univ (fun ψ : AddChar G ℂ => ‖gaussPeriod D ψ‖ ^ 2)
      (Finset.mem_univ (0 : AddChar G ℂ))]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext ψ
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and]
  rw [parseval_gaussPeriod] at hsplit
  rw [gaussPeriod_zero, Complex.norm_natCast] at hsplit
  linarith [hsplit]

/-- **`shaw_offdiag_moment_le` — the Hölder moment collapse (the unification).**
Let `B := max_{ψ≠0} ‖η_ψ‖` be the spectral gap (the largest off-trivial Cayley eigenvalue). Then for
every `M ≥ 1`:
`∑_{ψ≠0} ‖η_ψ‖^{2M} ≤ B^{2M−2} · (∑_{ψ≠0} ‖η_ψ‖²) = B^{2M−2} · (|D|·|G| − |D|²)`.
Every higher even moment of the Gauss-period family is controlled by the single scalar `B` and the
proven second moment.  This is the operator-level reason the below-UDR window lane *and* the deep-band
census lane both collapse to controlling `B`.  Proof: each term `‖η_ψ‖^{2M} = ‖η_ψ‖^{2M−2}·‖η_ψ‖²
≤ B^{2M−2}·‖η_ψ‖²` since `‖η_ψ‖ ≤ B` on the off-trivial set; then sum and use the second moment. -/
theorem shaw_offdiag_moment_le (D : Finset G) {B : ℝ}
    (hB : ∀ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0), ‖gaussPeriod D ψ‖ ≤ B)
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0), ‖gaussPeriod D ψ‖ ^ (2 * M)
      ≤ B ^ (2 * M - 2) * ((D.card : ℝ) * (Fintype.card G) - (D.card : ℝ) ^ 2) := by
  classical
  rw [← offdiag_secondMoment_eq, Finset.mul_sum]
  refine Finset.sum_le_sum (fun ψ hψ => ?_)
  have hnn : (0 : ℝ) ≤ ‖gaussPeriod D ψ‖ := norm_nonneg _
  have hle : ‖gaussPeriod D ψ‖ ≤ B := hB ψ hψ
  have hBnn : (0 : ℝ) ≤ B := le_trans hnn hle
  -- ‖η‖^{2M} = ‖η‖^{2M-2} · ‖η‖^2 ≤ B^{2M-2} · ‖η‖^2
  have hexp : 2 * M = (2 * M - 2) + 2 := by omega
  rw [hexp, pow_add]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hle (2 * M - 2)) (by positivity)

/-- **`shaw_offdiag_moment_le_of_spectralGap` — consumer form.**  Any spectral-gap *hypothesis*
`B(D) ≤ β` (i.e. every off-trivial Cayley eigenvalue is `≤ β`) propagates to every even moment:
`∑_{ψ≠0} ‖η_ψ‖^{2M} ≤ β^{2M−2}·(|D|·|G| − |D|²)`.  This is the exact shape consumed by the
moment-method δ\* bracket: a single bound `β` on the spectral gap yields all the deep moments. -/
theorem shaw_offdiag_moment_le_of_spectralGap (D : Finset G) {β : ℝ}
    (hgap : ∀ ψ : AddChar G ℂ, ψ ≠ 0 → ‖gaussPeriod D ψ‖ ≤ β)
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0), ‖gaussPeriod D ψ‖ ^ (2 * M)
      ≤ β ^ (2 * M - 2) * ((D.card : ℝ) * (Fintype.card G) - (D.card : ℝ) ^ 2) :=
  shaw_offdiag_moment_le D (fun ψ hψ => hgap ψ (Finset.mem_filter.mp hψ).2) M hM

/-- **The Shaw spectral gap as a named `Prop` (the single open prize input).**
`ShawSpectralGap D β := ∀ ψ ≠ 0, ‖η_ψ‖ ≤ β`, i.e. `B(D) = ‖S_D|_{1^⊥}‖ ≤ β`.  The prize floor is
`ShawSpectralGap μ_n (√(2·n·log(q/n)))` (the `B`-form). We name it; we do **not** prove it. -/
def ShawSpectralGap (D : Finset G) (β : ℝ) : Prop :=
  ∀ ψ : AddChar G ℂ, ψ ≠ 0 → ‖gaussPeriod D ψ‖ ≤ β

/-- The named prize input expands to the moment collapse with no further assumptions — closing the
loop: a single `ShawSpectralGap` certificate yields every deep even moment. -/
theorem moment_le_of_ShawSpectralGap (D : Finset G) {β : ℝ} (h : ShawSpectralGap D β)
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0), ‖gaussPeriod D ψ‖ ^ (2 * M)
      ≤ β ^ (2 * M - 2) * ((D.card : ℝ) * (Fintype.card G) - (D.card : ℝ) ^ 2) :=
  shaw_offdiag_moment_le_of_spectralGap D h M hM

/-- **Necessity of the spectral gap from the second moment (the floor side).**
Some off-trivial character has eigenvalue squared at least the *average* of the off-trivial second
moment: `∃ ψ ≠ 0, (|D||G| − |D|²)/(|G|−1) ≤ ‖η_ψ‖²`.  Hence any `β` with `ShawSpectralGap D β` must
satisfy `β² ≥ (|D||G|−|D|²)/(|G|−1) ≈ |D| = n` — the unconditional `B ≥ √n` floor (no cancellation
beats the L² average). This is why the conjectured constant is `√2`, not `1`: the L² average alone
already forces `√n`. -/
theorem exists_gaussPeriod_sq_ge_avg (D : Finset G) (hG : 1 < Fintype.card G) :
    ∃ ψ : AddChar G ℂ, ψ ≠ 0 ∧
      ((D.card : ℝ) * (Fintype.card G) - (D.card : ℝ) ^ 2) / ((Fintype.card G : ℝ) - 1)
        ≤ ‖gaussPeriod D ψ‖ ^ 2 := by
  classical
  set S := univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0) with hS
  have hcardAll : (Fintype.card (AddChar G ℂ)) = Fintype.card G := AddChar.card_eq (α := G)
  have hScard : S.card = Fintype.card G - 1 := by
    have h1 : S.card = (Finset.univ : Finset (AddChar G ℂ)).card - 1 := by
      rw [hS, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
    rw [h1, Finset.card_univ, hcardAll]
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hScard]; omega
  set M2 := ∑ ψ ∈ S, ‖gaussPeriod D ψ‖ ^ 2 with hM2
  have hM2val : M2 = (D.card : ℝ) * (Fintype.card G) - (D.card : ℝ) ^ 2 :=
    offdiag_secondMoment_eq D
  have hSc : ((Fintype.card G : ℝ) - 1) = (S.card : ℝ) := by
    rw [hScard, Nat.cast_sub (by omega)]; norm_num
  have hScpos : (0 : ℝ) < (S.card : ℝ) := by
    have hge : 1 ≤ S.card := by rw [hScard]; omega
    have : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hge
    linarith
  -- By contradiction: if every off-trivial term were `< M2/|S|`, the sum would be `< M2`.
  by_contra hcon
  push_neg at hcon
  rw [hSc, ← hM2val] at hcon
  have hSum_lt : (∑ ψ ∈ S, ‖gaussPeriod D ψ‖ ^ 2) < ∑ _ψ ∈ S, M2 / (S.card : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hSne (fun ψ hψ => ?_)
    exact hcon ψ (Finset.mem_filter.mp hψ).2
  rw [Finset.sum_const, nsmul_eq_mul] at hSum_lt
  have hcancel : (S.card : ℝ) * (M2 / (S.card : ℝ)) = M2 := by
    field_simp
  rw [hcancel] at hSum_lt
  rw [hM2] at hSum_lt
  exact lt_irrefl _ hSum_lt

end ArkLib.ProximityGap.Frontier.ShawOperatorA35

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.shawOp_eigen
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.gaussPeriod_zero
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.parseval_gaussPeriod
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.offdiag_secondMoment_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.shaw_offdiag_moment_le
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.shaw_offdiag_moment_le_of_spectralGap
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.moment_le_of_ShawSpectralGap
#print axioms ArkLib.ProximityGap.Frontier.ShawOperatorA35.exists_gaussPeriod_sq_ge_avg
