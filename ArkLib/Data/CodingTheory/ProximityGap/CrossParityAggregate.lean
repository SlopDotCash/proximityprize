/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion
import ArkLib.Data.CodingTheory.ProximityGap.DyadicHalvingRecursion

/-!
# The aggregate cross-parity (butterfly cross-term) identity (#407, lane F / Pan–Xu split)

## What this file proves

The dyadic FFT butterfly splits a level-`(i+1)` subgroup Gauss sum into its two level-`i`
children: with `H = G ∪ ζ•G` (disjoint),
`η_b(H) = η_b(G) + η_{ζb}(G)` (`eta_union_dilate`). Squaring,
`‖η_b(H)‖² = ‖η_b(G)‖² + ‖η_{ζb}(G)‖² + X(b)`,
where the **cross-parity term**
`X(b) := ‖η_b(H)‖² − ‖η_b(G)‖² − ‖η_{ζb}(G)‖² = 2·Re(η_b(G)·conj η_{ζb}(G))`
is the alignment excess — the *cross-parity* contribution to the far-line incidence whose
worst case is the open BGK sup-norm wall (`SubgroupGaussSumDilationRecursion`: the `√2`-vs-`2`
gap is the open core).

This file isolates the **first moment** of the cross-parity term — the part that is *clean,
exact, and `q`-independent*, in contrast to the worst case (`L^∞`) and the energy (`L²`), both
of which are the open BGK object. The two headline identities:

* `crossTerm_sum_zero` — **the full aggregate vanishes**:  `∑_{b∈F} X(b) = 0`.
  Pure Parseval: `∑_b ‖η_b(H)‖² = q·|H| = q·2|G| = ∑_b ‖η_b(G)‖² + ∑_b ‖η_{ζb}(G)‖²`, the dilate
  reindex `b ↦ ζb` (a bijection of `F`) making the third sum equal to the second.
* `crossTerm_sum_nonzero_eq` — **the off-zero aggregate is exactly `−2|G|²`**:
  `∑_{b≠0} X(b) = −2·|G|²`, because the only frequency carrying positive cross-parity *in
  aggregate* is `b = 0` (`X(0) = |H|² − 2|G|² = (2|G|)² − 2|G|² = 2|G|²`).

## The honest localization (the laneF result, three outcomes)

* **LANDED clean cross-parity identity** (this file): the *first moment* of the cross-parity term
  is exactly `−2|G|²`, `q`-independent — and **negative**. So *on aggregate the cross-parity term
  SUPPRESSES, it does not amplify*: the butterfly children are anti-aligned on average across
  frequencies. This is the exact, provable cross-parity bound the lane sought.
* **REFUTED localization hope** (`docs`/probe, see DISPROOF_LOG): the conjecture that the
  *positive* (amplifying) cross-parity is confined to `O(log n)` imprimitive frequencies is FALSE
  in the frequency picture — numerically the positive part `∑_{X(b)>0} X(b)` spreads over `Θ(q)`
  frequencies (`probe_crossparity_localize.py`). The aggregate is held negative by an even larger
  negative mass, not by sparsity of the positive part.
* **PRECISE reduction to the named core**: the *worst single-frequency* cross term
  `max_b X(b)` and the *energy* `∑_b X(b)²` are NOT `q`-independent (the latter grows like
  `q·E₂(G)`); these are exactly the BGK / additive-energy sup-norm wall already named in
  `SubgroupGaussSumDilationRecursion` and `_DyadicDeviationDecayEnvelope`. The first moment being
  clean while the L²/L^∞ are open is the precise statement of *which* part of the cross-parity is
  elementary and which is the open core.

Everything here is `sorry`/`axiom`-free and axiom-clean (`propext, Classical.choice, Quot.sound`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- BGK: Bourgain–Glibichuk–Konyagin, character sums over subgroups (the open sup-norm wall).
-/

set_option linter.style.longLine false


open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The cross-parity (butterfly cross) term** at frequency `b` for the disjoint dilate split
`H = G ∪ ζ•G`:
`X(b) := ‖η_b(H)‖² − ‖η_b(G)‖² − ‖η_{ζb}(G)‖²`.
By the butterfly recursion this equals `2·Re(η_b(G)·conj η_{ζb}(G))`, the alignment excess. -/
noncomputable def crossTerm (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) (b : F) : ℝ :=
  ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 - ‖eta ψ G b‖ ^ 2 - ‖eta ψ G (ζ * b)‖ ^ 2

omit [DecidableEq F] in
/-- **Dilation-invariance of the second moment.** Reindexing the frequency by the bijection
`b ↦ ζ·b` (`ζ ≠ 0`) leaves the second moment unchanged:
`∑_b ‖η_{ζb}(G)‖² = ∑_b ‖η_b(G)‖²`. This is the one nontrivial Parseval input particular to the
dilate child. -/
theorem sum_norm_sq_dilate_freq {ψ : AddChar F ℂ} (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) :
    ∑ b : F, ‖eta ψ G (ζ * b)‖ ^ 2 = ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  apply Fintype.sum_equiv (Equiv.mulLeft₀ ζ hζ)
  intro b
  rfl

/-- **The cross-parity term has zero first moment over `b = 0` too.** Useful staging: the two
diagonal second moments and the union second moment, after the dilate reindex, are all `q·|G|`
and `q·|H|`. -/
theorem sum_crossTerm_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) :
    ∑ b : F, crossTerm ψ G ζ b
      = (Fintype.card F : ℝ) * (G ∪ dilate ζ G).card
        - 2 * ((Fintype.card F : ℝ) * G.card) := by
  unfold crossTerm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      subgroup_gaussSum_secondMoment hψ (G ∪ dilate ζ G),
      subgroup_gaussSum_secondMoment hψ G,
      sum_norm_sq_dilate_freq G hζ,
      subgroup_gaussSum_secondMoment hψ G]
  ring

/-- **The full aggregate cross-parity vanishes: `∑_{b∈F} X(b) = 0`.** Pure Parseval: the union
second moment `q·|H|` equals `q·2|G|`, exactly the two diagonal second moments (the dilate child's
equal to the original by `sum_norm_sq_dilate_freq`). So averaged over *all* frequencies the
butterfly children carry no net cross-parity. -/
theorem crossTerm_sum_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b : F, crossTerm ψ G ζ b = 0 := by
  rw [sum_crossTerm_eq hψ G hζ, Finset.card_union_of_disjoint hdisj, card_dilate hζ G]
  push_cast
  ring

/-- **The cross-parity term at the trivial frequency: `X(0) = 2·|G|²`.** Here every period is its
cardinality (`η_b(K) = |K|` at `b = 0`), and `|H| = |G ∪ ζ•G| = 2|G|`, so
`X(0) = (2|G|)² − |G|² − |G|² = 2|G|²`. This is the entire positive aggregate cross-parity:
combined with `crossTerm_sum_zero` it forces the off-zero aggregate to be `−2|G|²`. -/
theorem crossTerm_zero_eq (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    crossTerm ψ G ζ 0 = 2 * (G.card : ℝ) ^ 2 := by
  have hz : ∀ K : Finset F, eta ψ K 0 = (K.card : ℂ) := by
    intro K
    simp [eta, AddChar.map_zero_eq_one]
  unfold crossTerm
  rw [mul_zero]
  simp only [hz, Complex.norm_natCast]
  rw [Finset.card_union_of_disjoint hdisj, card_dilate hζ G]
  push_cast
  ring

/-- **THE CLEAN CROSS-PARITY IDENTITY (headline).** The first moment of the cross-parity term over
all *nonzero* frequencies is exactly `−2·|G|²`:
`∑_{b≠0} X(b) = −2·|G|²`.
This is **`q`-independent** and **negative** — on aggregate across frequencies the butterfly cross
term *suppresses*, never amplifies. It is the exact, elementary (Parseval-only) content of the
cross-parity contribution to the far-line incidence. The complementary worst-case (`L^∞`) and
energy (`L²`) of `X` are NOT `q`-independent and are the open BGK sup-norm core (see the module
docstring and `SubgroupGaussSumDilationRecursion`). -/
theorem crossTerm_sum_nonzero_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b ∈ (Finset.univ.erase (0 : F)), crossTerm ψ G ζ b = -2 * (G.card : ℝ) ^ 2 := by
  have hfull : ∑ b : F, crossTerm ψ G ζ b = 0 := crossTerm_sum_zero hψ G hζ hdisj
  have hsplit : ∑ b : F, crossTerm ψ G ζ b
      = crossTerm ψ G ζ 0 + ∑ b ∈ (Finset.univ.erase (0 : F)), crossTerm ψ G ζ b := by
    rw [Finset.add_sum_erase Finset.univ (crossTerm ψ G ζ) (Finset.mem_univ 0)]
  rw [hsplit, crossTerm_zero_eq ψ G hζ hdisj] at hfull
  linarith

/-- **The aggregate cross-parity is bounded in `L¹` from below by its (negative) first moment.**
Trivial restatement making the suppression direction explicit and reusable: the off-zero
cross-parity sum is exactly `−2|G|²` and in particular `≤ 0`. Any future per-frequency *positive*
excess at some `b` must be paid for by at least equal negative excess elsewhere. -/
theorem crossTerm_sum_nonzero_nonpos {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b ∈ (Finset.univ.erase (0 : F)), crossTerm ψ G ζ b ≤ 0 := by
  rw [crossTerm_sum_nonzero_eq hψ G hζ hdisj]
  have : (0:ℝ) ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  linarith

/-!
## Non-vacuity: the dyadic 2-power subgroup tower realizes the hypotheses

The hypotheses `ζ ≠ 0` and `Disjoint G (dilate ζ G)` are **genuinely satisfiable** in the prize
regime, not vacuous: take `G = μ_k` (the `k`-th roots of unity) and `ζ` a primitive `2k`-th root
(`ζ^k = -1`). Then `dilate ζ μ_k = ζ·μ_k = μ_k^{(-1)}` (the "negative half", `{x : x^k = -1}`),
which is disjoint from `μ_k` in odd characteristic (`(1:F) ≠ -1`), and `μ_k ∪ ζ·μ_k = μ_{2k}`.
This is exactly the `eta_halving` split. Hence the clean cross-parity identity applies to the
actual dyadic Gaussian-period tower. -/

/-- **The dyadic split realizes the dilate-union hypotheses.** For `ζ^k = -1` in odd characteristic,
`μ_k` and its `ζ`-dilate are disjoint and their union is `μ_{2k}`. This certifies that
`crossTerm_sum_nonzero_eq` is non-vacuous for the prize-regime dyadic subgroup. -/
theorem dyadic_dilate_split {ζ : F} (k : ℕ) (hk : 0 < k) (htwo : (1 : F) ≠ -1) (hζ : ζ ^ k = -1) :
    Disjoint (Polynomial.nthRootsFinset k (1 : F))
        (dilate ζ (Polynomial.nthRootsFinset k (1 : F)))
      ∧ Polynomial.nthRootsFinset k (1 : F) ∪ dilate ζ (Polynomial.nthRootsFinset k (1 : F))
          = Polynomial.nthRootsFinset (2 * k) (1 : F) := by
  have h2k : 0 < 2 * k := by omega
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, zero_pow hk.ne'] at hζ; exact (by norm_num : (0:F) ≠ -1) hζ
  -- the dilate ζ•μ_k equals the "negative half" {x : x^k = -1}
  have himg : dilate ζ (Polynomial.nthRootsFinset k (1 : F))
      = Polynomial.nthRootsFinset k (-1 : F) := by
    unfold dilate
    ext x
    simp only [Finset.mem_image, Polynomial.mem_nthRootsFinset hk]
    constructor
    · rintro ⟨y, hy, rfl⟩; rw [mul_pow, hζ, hy]; ring
    · intro hxk
      refine ⟨ζ⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]⟩
      rw [mul_pow, inv_pow, hζ, hxk]; simp
  refine ⟨?_, ?_⟩
  · rw [himg, Finset.disjoint_left]
    intro x hx hx'
    rw [Polynomial.mem_nthRootsFinset hk] at hx
    rw [Polynomial.mem_nthRootsFinset hk] at hx'
    exact htwo (hx.symm.trans hx')
  · rw [himg]
    ext x
    simp only [Finset.mem_union, Polynomial.mem_nthRootsFinset hk,
      Polynomial.mem_nthRootsFinset h2k]
    constructor
    · rintro (h | h) <;> rw [two_mul, pow_add, h] <;> ring
    · intro hx
      have hsq : x ^ k * x ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hx
      exact mul_self_eq_one_iff.mp hsq

/-- **The clean cross-parity identity, realized on the dyadic subgroup tower (non-vacuous form).**
For the actual dyadic Gaussian period over `μ_{2k} = μ_k ⊔ ζ·μ_k` (`ζ^k = -1`, odd char), the
first moment of the butterfly cross-parity term over the nonzero frequencies is exactly
`−2·|μ_k|²`. This instantiates `crossTerm_sum_nonzero_eq` with the prize-regime dyadic split
certified by `dyadic_dilate_split`, so the identity is not vacuously true. -/
theorem crossTerm_sum_nonzero_eq_dyadic {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ζ : F} (k : ℕ)
    (hk : 0 < k) (htwo : (1 : F) ≠ -1) (hζ : ζ ^ k = -1) :
    ∑ b ∈ (Finset.univ.erase (0 : F)),
        crossTerm ψ (Polynomial.nthRootsFinset k (1 : F)) ζ b
      = -2 * ((Polynomial.nthRootsFinset k (1 : F)).card : ℝ) ^ 2 := by
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, zero_pow hk.ne'] at hζ; exact (by norm_num : (0:F) ≠ -1) hζ
  exact crossTerm_sum_nonzero_eq hψ _ hζ0 (dyadic_dilate_split k hk htwo hζ).1

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.sum_norm_sq_dilate_freq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.crossTerm_sum_zero
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.crossTerm_zero_eq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.crossTerm_sum_nonzero_eq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.crossTerm_sum_nonzero_nonpos
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dyadic_dilate_split
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.crossTerm_sum_nonzero_eq_dyadic
