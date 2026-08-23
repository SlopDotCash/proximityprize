/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCKHS25.Interpolation
import ArkLib.Data.CodingTheory.ProximityGap.BCKHS25.CollinearProximates
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# From the [BCKHS25] joint proximate to affine-line `jointAgreement`

The Hensel-free [BCKHS25] §2 route produces a single degree-`< deg` polynomial
pair `(p₀, p₁)` whose *joint* disagreement with the line word `(u₀, u₁)` is
small (Theorem 2.2 / Claim 2.3, `BCKHS25.proximity_gap_listDecoding` /
`exists_joint_proximate`). This file converts that joint-agreement bound into
the coding-theoretic `jointAgreement` predicate (the `Fin 2`/affine-line case of
`InterleavedCode.jointAgreement`): a common large agreement set together with two
codewords of the Reed–Solomon code.

This is the consumer-side bridge: it is exactly the output shape demanded by the
list-decoding branch of `δ_ε_correlatedAgreementAffineLines`, supplied here from
the Hensel-free joint pair rather than the §5 Hensel coefficient extraction.
-/

namespace BCKHS25

set_option linter.unusedSectionVars false

open NNReal Code Polynomial
open scoped LinearCode

variable {ι F : Type}

/-- The two-row word stack of a line word `(u₀, u₁)`. -/
noncomputable def lineWordStack (u₀ u₁ : ι → F) : WordStack F (Fin 2) ι :=
  Matrix.of (fun (i : Fin 2) => if i = 0 then u₀ else u₁)

@[simp] lemma lineWordStack_zero (u₀ u₁ : ι → F) : lineWordStack u₀ u₁ 0 = u₀ := rfl
@[simp] lemma lineWordStack_one (u₀ u₁ : ι → F) : lineWordStack u₀ u₁ 1 = u₁ := rfl

variable [Fintype ι] [Nonempty ι]
variable [Field F] [Finite F] [DecidableEq F]

/-- **Joint pair ⟹ affine-line `jointAgreement`.** A degree-`< deg` polynomial
pair `(p₀, p₁)` whose joint disagreement set with the line word `(u₀, u₁)` has
at most `Nat.floor (δ · n)` points yields the `jointAgreement` predicate for the
two-row stack `(u₀, u₁)` against the Reed–Solomon code: the common agreement set
has size `≥ (1 − δ)·n`, and `p₀, p₁` give the two required codewords.

Derivation: the agreement set `S = {x | p₀(domain x) = u₀ x ∧ p₁(domain x) = u₁ x}`
is the complement of the joint disagreement set, so
`|S| = n − |disagreement| ≥ n − ⌊δ·n⌋ ≥ (1−δ)·n`; and `evalOnPoints domain pᵢ`
is an RS codeword since `degree pᵢ < deg`. -/
theorem jointAgreement_of_jointDisagreement_le {deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ : ℝ≥0} {u₀ u₁ : ι → F} {p₀ p₁ : F[X]}
    (hp₀ : p₀.natDegree < deg) (hp₁ : p₁.natDegree < deg)
    (hdis : (Finset.univ.filter
      (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))).card
        ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0))) :
    jointAgreement (F := F) (κ := Fin 2) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (W := lineWordStack u₀ u₁) := by
  classical
  haveI := Fintype.ofFinite F
  set n := Fintype.card ι with hn
  -- agreement set: complement of the joint disagreement set
  set Dis : Finset ι := Finset.univ.filter
    (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x)) with hDis
  set Agr : Finset ι := Finset.univ.filter
    (fun x => p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x) with hAgr
  have hsplit : Agr.card + Dis.card = n := by
    rw [hAgr, hDis, hn, Finset.card_filter_add_card_filter_not]
    simp
  -- |Agr| = n − |Dis| ≥ n − ⌊δ·n⌋
  have hAgr_card_nat : n - Nat.floor (δ * (n : ℝ≥0)) ≤ Agr.card := by
    have : Dis.card ≤ Nat.floor (δ * (n : ℝ≥0)) := by simpa [hn] using hdis
    omega
  -- cardinality lower bound in ℝ≥0: |Agr| ≥ (1 − δ)·n
  have hAgr_real : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (Agr.card : ℝ≥0) := by
    -- (1 − δ)·n ≤ n − ⌊δ·n⌋ ≤ |Agr|
    have hfloor : ((Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) ≤ δ * (n : ℝ≥0) :=
      Nat.floor_le (by positivity)
    have hstep : (1 - δ) * (n : ℝ≥0) ≤ (n : ℝ≥0) - ((Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) := by
      rw [tsub_mul, one_mul]
      exact tsub_le_tsub_left hfloor _
    refine le_trans hstep ?_
    -- n − ⌊δ·n⌋ ≤ |Agr| via the ℕ inequality, cast to ℝ≥0
    have hcast : ((n - Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) ≤ (Agr.card : ℝ≥0) := by
      exact_mod_cast hAgr_card_nat
    refine le_trans ?_ hcast
    -- (n : ℝ≥0) − (⌊..⌋ : ℝ≥0) ≤ ((n − ⌊..⌋ : ℕ) : ℝ≥0) : standard cast-of-sub bound
    rw [tsub_le_iff_right, ← Nat.cast_add]
    have : n ≤ (n - Nat.floor (δ * (n : ℝ≥0))) + Nat.floor (δ * (n : ℝ≥0)) := by omega
    exact_mod_cast this
  -- the two RS codewords
  have hcw₀ : (fun x => p₀.eval (domain x)) ∈ ReedSolomon.code domain deg := by
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    exact ⟨p₀, hp₀, rfl⟩
  have hcw₁ : (fun x => p₁.eval (domain x)) ∈ ReedSolomon.code domain deg := by
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    exact ⟨p₁, hp₁, rfl⟩
  refine ⟨Agr, hAgr_real, fun i => if i = 0 then (fun x => p₀.eval (domain x))
    else (fun x => p₁.eval (domain x)), ?_⟩
  intro i
  fin_cases i
  · refine ⟨by simpa using hcw₀, ?_⟩
    intro x hx
    simp only [hAgr, Finset.mem_filter] at hx
    simpa [lineWordStack] using hx.2.1
  · refine ⟨by simpa using hcw₁, ?_⟩
    intro x hx
    simp only [hAgr, Finset.mem_filter] at hx
    simpa [lineWordStack] using hx.2.2

/-- **[BCKHS25] §2 Hensel-free affine-line `jointAgreement` (end-to-end).**

Direct consumer closure: from the per-`z` list-decoding hypothesis (`prox`: a
large set `S` of curve parameters, each with a degree-`k` proximate within
Hamming distance `e` of the line combination `u₀ + u₁·z`) together with the
Polishchuk–Spielman ratio (`hratio`) and degree budget (`hn`, `hDZ`), the line
word `(u₀, u₁)` has `jointAgreement` with the Reed–Solomon code of degree
`deg = k + 1`, provided the joint-agreement loss `e + h` fits inside the
proximity radius `⌊δ·n⌋`.

This chains [BCKHS25] Claim 2.3 (`exists_joint_proximate`, built on Lemma 2.1's
Berlekamp–Welch pair) with the joint-pair → `jointAgreement` bridge, giving the
list-decoding-branch output of `δ_ε_correlatedAgreementAffineLines` entirely on
the Hensel-free route. -/
theorem jointAgreement_of_proximates (k e h DZ : ℕ) {δ : ℝ≥0}
    (hn : k + 2 * e + h + 1 = Fintype.card ι)
    (hDZ : e + 1 ≤ (h + 1) * DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F) (hS0 : 0 < S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e)
    (hratio : ((k + e + h : ℕ) : ℚ) / (Fintype.card ι : ℚ)
      + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1)
    (hfit : e + h ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0))) :
    jointAgreement (F := F) (κ := Fin 2) (ι := ι)
      (C := ReedSolomon.code domain (k + 1)) (δ := δ) (W := lineWordStack u₀ u₁) := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨p₀, p₁, hp₀, hp₁, hdis⟩ :=
    exists_joint_proximate k e h DZ hn hDZ hDZ0 domain u₀ u₁ S hS0 prox hratio
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  have hp₀' : p₀.natDegree < k + 1 := Nat.lt_succ_of_le hp₀
  have hp₁' : p₁.natDegree < k + 1 := Nat.lt_succ_of_le hp₁
  exact jointAgreement_of_jointDisagreement_le (deg := k + 1) hp₀' hp₁'
    (le_trans hdis hfit)

/-- **[BCKHS25] §2 distance restoration (2.4 ∘ 2.2 chain).** Combining Theorem
2.2's uniform-in-`z` line closeness (`proximity_gap_listDecoding`) with Lemma 2.4
(`card_jointDisagreement_filter_mul_le`) sharpens the joint disagreement bound:
the SAME joint pair `(p₀, p₁)` produced by Claim 2.3 has joint disagreement `d`
with `(u₀, u₁)` satisfying `(|Z| − 1)·d ≤ |Z|·(e + h)` for every `z`-set `Z` of
size `≥ 2` — i.e. `d ≤ |Z|/(|Z| − 1)·(e + h)`, which beats the raw `e + h` bound
as `|Z|` grows. This is the oversized-error-locator distance restoration that
closes the [BCKHS25] §2 Berlekamp–Welch route. -/
theorem card_jointDisagreement_restored (k e h DZ : ℕ)
    (hn : k + 2 * e + h + 1 = Fintype.card ι)
    (hDZ : e + 1 ≤ (h + 1) * DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F) (hS0 : 0 < S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e)
    (hratio : ((k + e + h : ℕ) : ℚ) / (Fintype.card ι : ℚ)
      + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      (∀ (Zs : Finset F), 2 ≤ Zs.card →
        (Zs.card - 1) *
            (Finset.univ.filter
              (fun x => ¬(u₀ x = p₀.eval (domain x) ∧ u₁ x = p₁.eval (domain x)))).card
          ≤ Zs.card * (e + h)) := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨p₀, p₁, hp₀, hp₁, hclose⟩ :=
    proximity_gap_listDecoding k e h DZ hn hDZ hDZ0 domain u₀ u₁ S hS0 prox hratio
  refine ⟨p₀, p₁, hp₀, hp₁, fun Zs hZ => ?_⟩
  -- Lemma 2.4 with the evaluated codeword pair, fed Theorem 2.2's per-z closeness
  refine card_jointDisagreement_filter_mul_le (u₀ := u₀) (u₁ := u₁)
    (p₀ := fun x => p₀.eval (domain x)) (p₁ := fun x => p₁.eval (domain x))
    (e := e + h) Zs hZ (fun z _ => ?_)
  -- the keystone's bound is stated with `(p₀ + C z * p₁).eval`; rewrite to `q₀ + z·q₁`
  have hpt : (fun x => (p₀ + Polynomial.C z * p₁).eval (domain x))
      = (fun x => p₀.eval (domain x) + z * p₁.eval (domain x)) := by
    funext x
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have := hclose z
  rwa [hpt] at this

/-- **[BCKHS25] §2 restored-distance affine-line `jointAgreement`.**

This is the consumer form of `card_jointDisagreement_restored`: if the restored
bound
`(|S| - 1) * d ≤ |S| * (e + h)`
fits inside the target proximity radius, i.e.
`|S| * (e + h) ≤ (|S| - 1) * ⌊δ n⌋`, then the same Hensel-free
Berlekamp-Welch/Polishchuk-Spielman route yields `jointAgreement` for the
two-row affine-line stack. -/
theorem jointAgreement_of_proximates_restored (k e h DZ : ℕ) {δ : ℝ≥0}
    (hn : k + 2 * e + h + 1 = Fintype.card ι)
    (hDZ : e + 1 ≤ (h + 1) * DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F)
    (hS2 : 2 ≤ S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e)
    (hratio : ((k + e + h : ℕ) : ℚ) / (Fintype.card ι : ℚ)
      + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1)
    (hfit :
      S.card * (e + h) ≤
        (S.card - 1) * Nat.floor (δ * (Fintype.card ι : ℝ≥0))) :
    jointAgreement (F := F) (κ := Fin 2) (ι := ι)
      (C := ReedSolomon.code domain (k + 1)) (δ := δ) (W := lineWordStack u₀ u₁) := by
  classical
  haveI := Fintype.ofFinite F
  have hS0 : 0 < S.card := by omega
  obtain ⟨p₀, p₁, hp₀, hp₁, hrestored⟩ :=
    card_jointDisagreement_restored k e h DZ hn hDZ hDZ0 domain u₀ u₁ S hS0 prox hratio
  have hrestoredS := hrestored S hS2
  have hpos : 0 < S.card - 1 := by omega
  have hdis_oriented :
      (Finset.univ.filter
        (fun x => ¬(u₀ x = p₀.eval (domain x) ∧ u₁ x = p₁.eval (domain x)))).card
        ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := by
    refine le_of_mul_le_mul_left ?_ hpos
    exact le_trans hrestoredS hfit
  have hfilter :
      Finset.univ.filter
        (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))
        =
      Finset.univ.filter
        (fun x => ¬(u₀ x = p₀.eval (domain x) ∧ u₁ x = p₁.eval (domain x))) := by
    apply Finset.filter_congr
    intro x _hx
    constructor
    · intro h h'
      exact h ⟨h'.1.symm, h'.2.symm⟩
    · intro h h'
      exact h ⟨h'.1.symm, h'.2.symm⟩
  have hdis :
      (Finset.univ.filter
        (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))).card
        ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := by
    rwa [hfilter]
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  exact jointAgreement_of_jointDisagreement_le (deg := k + 1)
    (Nat.lt_succ_of_le hp₀) (Nat.lt_succ_of_le hp₁) hdis

end BCKHS25
