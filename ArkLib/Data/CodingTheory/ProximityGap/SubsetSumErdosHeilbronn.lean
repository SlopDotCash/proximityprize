/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumRadiusOne
import ArkLib.ToMathlib.RestrictedSumset

/-!
# Erdős–Heilbronn floor for the radius-one MCA error (`k = 1`)

This file combines the two ingredients

* `ProximityGap.epsMCA_one_ge_card_subsetSums` (unconditional subset-sum floor for `ε_mca(RS,1)`),
* `MvPolynomial.erdos_heilbronn_two` (the `h = 2` Erdős–Heilbronn restricted-sumset bound),

into a **lower bound with explicit additive content** for Reed–Solomon codes of degree `k = 1`
over prime fields. Concretely, for `RS[F, domain, 1]` over a finite field `F` of prime
characteristic `p` with `n := |ι|` evaluation points, `2 ≤ n`, and `2(n - 2) < p`:

  `ε_mca(RS[F, domain, 1], 1) ≥ (2(n - 2) + 1) / q`   (`epsMCA_one_ge_erdos_heilbronn`)

and consequently the formal §1 MCA prize is refuted whenever `q < 2^128 · (2(n - 2) + 1)`
(`epsStar_lt_epsMCA_one_of_erdos_heilbronn`).

This is strictly stronger than the spike floor `min(n - k, q)/q` for the linear band `k = 1`,
since `2(n - 2) + 1 ≈ 2n` exceeds `n - 1`.

## References

- [Alon_1999]; Erdős–Heilbronn; Dias da Silva–Hamidoune.
- [ABF26] Arnon, Boneh, Fenzi.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped BigOperators ENNReal

section EH

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The `2`-subset-sum set of an injective evaluation domain contains the Erdős–Heilbronn
restricted sumset of its image. Hence its cardinality is at least as large. -/
lemma restrictedSumset2_subset_subsetSumsKplus1 (domain : ι ↪ F) :
    MvPolynomial.restrictedSumset2 (Finset.image (fun i => domain i) Finset.univ)
      ⊆ subsetSumsKplus1 domain 1 := by
  classical
  intro γ hγ
  rw [MvPolynomial.restrictedSumset2, Finset.mem_image] at hγ
  obtain ⟨S, hS, rfl⟩ := hγ
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSsub, hScard⟩ := hS
  -- `S = {a, b}` with `a ≠ b`, both in the image of `domain`.
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hScard
  have ha : a ∈ Finset.image (fun i => domain i) Finset.univ :=
    hSsub (Finset.mem_insert_self _ _)
  have hb : b ∈ Finset.image (fun i => domain i) Finset.univ :=
    hSsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [Finset.mem_image] at ha hb
  obtain ⟨i, -, hia⟩ := ha
  obtain ⟨j, -, hjb⟩ := hb
  -- `i ≠ j` since `domain i = a ≠ b = domain j`.
  have hij : i ≠ j := by
    intro h; apply hab; rw [← hia, ← hjb, h]
  -- `{i, j}` is a 2-subset of `ι` with sum `domain i + domain j = a + b`.
  rw [subsetSumsKplus1, Finset.mem_image]
  refine ⟨{i, j}, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, Finset.card_pair hij⟩
  · rw [Finset.sum_pair hij, hia, hjb, Finset.sum_pair hab]

/-- The image of an injective `domain` has cardinality `n := |ι|`. -/
lemma card_image_domain (domain : ι ↪ F) :
    (Finset.image (fun i => domain i) Finset.univ).card = Fintype.card ι := by
  rw [Finset.card_image_of_injective _ domain.injective, Finset.card_univ]

/-- **Erdős–Heilbronn floor for `ε_mca(RS, 1)` at `k = 1`.** For `RS[F, domain, 1]` over a finite
field `F` of prime characteristic `p`, with `n := |ι| ≥ 2` and `2(n - 2) < p`:

  `ε_mca(RS[F, domain, 1], 1) ≥ (2(n - 2) + 1) / q`. -/
theorem epsMCA_one_ge_erdos_heilbronn (domain : ι ↪ F) {p : ℕ} (hp : p.Prime)
    (hchar : ringChar F = p) (hn : 2 ≤ Fintype.card ι) (hsmall : 2 * (Fintype.card ι - 2) < p) :
    ((2 * (Fintype.card ι - 2) + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain 1 : Set (ι → F)) 1 := by
  classical
  set n := Fintype.card ι with hn_def
  set A : Finset F := Finset.image (fun i => domain i) Finset.univ with hA
  have hAcard : A.card = n := card_image_domain domain
  have hEH : 2 * (n - 2) + 1 ≤ (MvPolynomial.restrictedSumset2 A).card := by
    have := MvPolynomial.erdos_heilbronn_two (F := F) hp hchar A
      (by rw [hAcard]; exact hn) (by rw [hAcard]; exact hsmall)
    rwa [hAcard] at this
  have hsubset : 2 * (n - 2) + 1 ≤ (subsetSumsKplus1 domain 1).card := by
    refine le_trans hEH ?_
    exact Finset.card_le_card (restrictedSumset2_subset_subsetSumsKplus1 domain)
  have hfloor := epsMCA_one_ge_card_subsetSums (F := F) domain (k := 1) (by omega)
  refine le_trans ?_ hfloor
  have hnum : ((2 * (n - 2) + 1 : ℕ) : ENNReal)
      ≤ ((subsetSumsKplus1 domain 1).card : ENNReal) := by exact_mod_cast hsubset
  exact ENNReal.div_le_div_right hnum _

/-- **Refutation of the §1 MCA prize via Erdős–Heilbronn at `k = 1`.** If `F` is a finite field
of prime characteristic `p` with `n := |ι| ≥ 2`, `2(n - 2) < p`, and
`q < 2^128 · (2(n - 2) + 1)`, then `ε* = 2^(-128) < ε_mca(RS[F, domain, 1], 1)`. -/
theorem epsStar_lt_epsMCA_one_of_erdos_heilbronn (domain : ι ↪ F) {p : ℕ} (hp : p.Prime)
    (hchar : ringChar F = p) (hn : 2 ≤ Fintype.card ι) (hsmall : 2 * (Fintype.card ι - 2) < p)
    (hq : Fintype.card F < 2 ^ (128 : ℕ) * (2 * (Fintype.card ι - 2) + 1)) :
    (ProximityGap.epsStar : ENNReal) <
      epsMCA (F := F) (A := F) (ReedSolomon.code domain 1 : Set (ι → F)) 1 := by
  classical
  set n := Fintype.card ι with hn_def
  set q := Fintype.card F with hq_def
  have hq_pos : 0 < q := Fintype.card_pos
  have hepsStar : (ProximityGap.epsStar : ENNReal) = (2 ^ (128 : ℕ) : ENNReal)⁻¹ := by
    rw [ProximityGap.epsStar]; push_cast; rw [one_div]
  rw [hepsStar]
  have hfloor := epsMCA_one_ge_erdos_heilbronn domain hp hchar hn hsmall
  rw [← hn_def, ← hq_def] at hfloor
  refine lt_of_lt_of_le ?_ hfloor
  set M : ℕ := 2 * (n - 2) + 1 with hM
  have hqne : (q : ENNReal) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hqne) (Or.inl hqtop)]
  have hpow_ne_zero : (2 ^ (128 : ℕ) : ENNReal) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (128 : ℕ) : ENNReal) ≠ ⊤ := by finiteness
  rw [← ENNReal.div_eq_inv_mul, ENNReal.div_lt_iff (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  have hcast : (q : ENNReal) < ((2 ^ (128 : ℕ) * M : ℕ) : ENNReal) := by exact_mod_cast hq
  calc (q : ENNReal) < ((2 ^ (128 : ℕ) * M : ℕ) : ENNReal) := hcast
    _ = (M : ENNReal) * (2 ^ (128 : ℕ) : ENNReal) := by push_cast; ring

end EH

end ProximityGap
