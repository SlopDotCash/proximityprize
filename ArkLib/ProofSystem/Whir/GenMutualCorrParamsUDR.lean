/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.RBRSoundness
import ArkLib.ProofSystem.Whir.MCARscPairUDR
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode

/-!
# A unique-decoding-regime instance of `WhirIOP.GenMutualCorrParams`

`WhirIOP.GenMutualCorrParams` (`RBRSoundness.lean`) is the assumption-carrying class that
threads "the pair power generator has mutual correlated agreement for every round/fold code"
through WHIR's Theorem 5.2 surface (`whir_rbr_soundness`, `WhirVectorIOPProof`). Until now it
had **no instance anywhere**: its `h` field at `BStar = √ρ` is ACFY24 Conjecture 4.12 (open).

This file constructs the first honest instance, in the **unique-decoding regime**:

* `BStar i j = (1 + ρᵢⱼ)/2` (the complement of the relative unique-decoding radius), and
* `errStar i j = (2 − 1)·2^{mᵢⱼ}/(ρᵢⱼ·|F|) = |ιᵢⱼ|/|F|`,

exactly the Corollary 4.11 bounds below the unique-decoding radius, discharged by the
(axiom-clean, unconditional) `MutualCorrAgreement.mca_rsc_pair_holds` (`MCARscPairUDR.lean`).
The list-decodability field is discharged at list size `1` (unique decoding) for the radius
`δ i = 1 − sup_j BStar i j`, via the from-scratch Reed–Solomon unique-decoding theorem
`ReedSolomon.unique_decode` (`ReedSolomonUniqueDecode.lean`).

The data the caller must supply is exactly the data the class itself stores: the per-round
power-domain embeddings `φ i j` (with their `Fintype`/`Nonempty`/`DecidableEq`/`Smooth`
instances) and the degree bound `2^{varCountᵢ − j} ≤ |ιᵢⱼ|`. Everything else — the MCA field,
the `parℓ = 2` cardinality pins, the admissible `δ`, and unique decodability — is **proven**.

This is the UDR-window instantiation flagged in the 2026-06-10 audit: it makes the WHIR
RBR-soundness chain consumable end-to-end in the unique-decoding regime. It does *not*
advance the `√ρ` (Johnson) conjecture surface, which remains open.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

namespace WhirIOP

open MutualCorrAgreement Generator ReedSolomon BlockRelDistance ListDecodable NNReal
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

section UniqueDecodable

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Fintype F] in
/-- **Smooth Reed–Solomon codes are uniquely decodable below the unique-decoding radius**
(list-decodability form, list size `1`): for any radius `δ ≤ (1 − ρ)/2` with `ρ = 2^m/|ι|`,
every Hamming ball of relative radius `δ` contains at most one codeword of
`RS[F, φ, 2^m]`. -/
theorem smoothCode_listDecodable_one (φ : ι ↪ F) [Smooth φ] (m : ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδle : (δ : ℝ) ≤ (1 - (2 : ℝ) ^ m / (Fintype.card ι : ℝ)) / 2) :
    listDecodable ((smoothCode φ m : Set (ι → F))) (δ : ℝ) ((1 : ℝ≥0) : ℝ) := by
  classical
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  intro y
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnpos
  -- the close-codeword set is a subsingleton
  have hsub : (closeCodewordsRel ((smoothCode φ m : Set (ι → F))) y (δ : ℝ)).Subsingleton := by
    rintro c ⟨hcC, hcB⟩ c' ⟨hc'C, hc'B⟩
    -- turn relative-distance membership into an absolute Hamming-distance bound
    have habs : ∀ {z : ι → F},
        z ∈ relHammingBall y (δ : ℝ) →
        hammingDist y z ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
      intro z hz
      simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist] at hz
      push_cast at hz
      rw [div_le_iff₀ hnR] at hz
      refine Nat.le_floor ?_
      -- the `Δ₀` in `hz` carries `relHammingBall`'s baked-in `Decidable` instances;
      -- bridge the (subsingleton) mismatch
      convert hz using 2
      congr!
    have hd : hammingDist y c ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := habs hcB
    have hd' : hammingDist y c' ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := habs hc'B
    -- the radius is within the unique-decoding bound `2e < n − 2^m + 1`
    have hfloor : (⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) :=
      Nat.floor_le (by positivity)
    have h2δ : 2 * (δ : ℝ) * (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) - 2 ^ m := by
      have hmul := mul_le_mul_of_nonneg_right
        (show 2 * (δ : ℝ) ≤ 1 - (2 : ℝ) ^ m / (Fintype.card ι : ℝ) by linarith [hδle]) hnR.le
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hnR)] at hmul
      linarith [hmul]
    have hcast : ((Fintype.card ι - 2 ^ m : ℕ) : ℝ)
        = (Fintype.card ι : ℝ) - (2 : ℝ) ^ m := by
      rw [Nat.cast_sub hk]
      push_cast
      ring
    have h2e : 2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι - 2 ^ m + 1 := by
      have hR : (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ : ℝ)
          ≤ ((Fintype.card ι - 2 ^ m : ℕ) : ℝ) := by
        rw [hcast]
        linarith [hfloor, h2δ]
      have hN : 2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ ≤ Fintype.card ι - 2 ^ m := by
        exact_mod_cast hR
      omega
    exact ReedSolomon.unique_decode (α := φ) (k := 2 ^ m) hk hcC hc'C hd hd' h2e
  -- a subsingleton has `ncard ≤ 1`
  rcases hsub.eq_empty_or_singleton with h | ⟨a, h⟩
  · rw [h, Set.ncard_empty]
    norm_num
  · rw [h, Set.ncard_singleton]
    norm_num

end UniqueDecodable

section Instance

variable {M : ℕ} {ι : Fin (M + 1) → Type}

/-- The per-round pair power generator (`parℓ = Fin 2`, exponents `(0, 1)`) on the
`j`-th power domain of round `i`. -/
noncomputable def pairUDRGen (P : Params ι F) (S : ∀ i : Fin (M + 1), Finset (ι i))
    (φ : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      indexPowT (S i) (P.φ i) (j : ℕ) ↪ F)
    (inst1 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      Fintype (indexPowT (S i) (P.φ i) (j : ℕ)))
    (inst2 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      Nonempty (indexPowT (S i) (P.φ i) (j : ℕ)))
    (inst3 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      DecidableEq (indexPowT (S i) (P.φ i) (j : ℕ)))
    (inst4 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)), Smooth (φ i j))
    (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)) :
    ProximityGenerator (indexPowT (S i) (P.φ i) (j : ℕ)) F :=
  letI := inst1 i j
  letI := inst2 i j
  letI := inst3 i j
  letI := inst4 i j
  RSGenerator.genRSC (Fin 2) (φ i j) (P.varCount i - (j : ℕ)) Fin.valEmbedding

/-- **The unique-decoding-window instance of `GenMutualCorrParams`.**

Given the per-round power-domain data (embeddings `φ i j` with their instances) and the
degree bounds `2^{varCountᵢ − j} ≤ |ιᵢⱼ|`, the WHIR mutual-correlated-agreement parameter
class is *constructible*, with the Corollary 4.11 unique-decoding bounds
`BStar = (1 + ρ)/2`, `errStar = 2^m/(ρ·|F|)` (both proven via `mca_rsc_pair_holds`), the
admissible radius `δ i = 1 − sup_j BStar i j` (the smallest relative unique-decoding radius
over the round's fold codes), and unique decodability (`dist i j = 1`). -/
@[reducible]
noncomputable def genMutualCorrParamsUDR (P : Params ι F)
    (S : ∀ i : Fin (M + 1), Finset (ι i))
    (φ : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      indexPowT (S i) (P.φ i) (j : ℕ) ↪ F)
    (inst1 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      Fintype (indexPowT (S i) (P.φ i) (j : ℕ)))
    (inst2 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      Nonempty (indexPowT (S i) (P.φ i) (j : ℕ)))
    (inst3 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      DecidableEq (indexPowT (S i) (P.φ i) (j : ℕ)))
    (inst4 : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)), Smooth (φ i j))
    (hk : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      2 ^ (P.varCount i - (j : ℕ)) ≤ @Fintype.card _ (inst1 i j)) :
    GenMutualCorrParams ι P S := by
  classical
  -- the rate identity, per round and fold level
  have hrate : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate
        = (2 : ℝ) ^ (P.varCount i - (j : ℕ)) / (@Fintype.card _ (inst1 i j) : ℝ) := by
    intro i j
    letI := inst1 i j
    letI := inst2 i j
    letI := inst3 i j
    letI := inst4 i j
    have h := rate_smoothCode_coe (φ i j) (P.varCount i - (j : ℕ)) (hk i j)
    simpa [pairUDRGen, RSGenerator.genRSC] using h
  have hrate_nonneg : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      0 ≤ (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate := by
    intro i j
    rw [hrate i j]
    positivity
  have hrate_le_one : ∀ (i : Fin (M + 1)) (j : Fin (P.foldingParam i + 1)),
      (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate ≤ 1 := by
    intro i j
    rw [hrate i j]
    haveI := inst1 i j
    haveI := inst2 i j
    have hpos : (0 : ℝ) < (@Fintype.card _ (inst1 i j) : ℝ) := by
      exact_mod_cast (@Fintype.card_pos _ (inst1 i j) (inst2 i j))
    rw [div_le_one hpos]
    exact_mod_cast hk i j
  refine
    { δ := fun i => 1 - Finset.univ.sup (fun j : Fin (P.foldingParam i + 1) =>
        Real.toNNReal ((1 + (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate) / 2)),
      dist := fun _ _ => 1,
      φ := φ,
      inst1 := inst1,
      inst2 := inst2,
      inst3 := inst3,
      inst4 := inst4,
      parℓ_type := fun _ _ => Fin 2,
      inst5 := fun _ _ => inferInstance,
      exp := fun _ _ => Fin.valEmbedding,
      Gen_α := pairUDRGen P S φ inst1 inst2 inst3 inst4,
      inst6 := fun i j => (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).hℓ,
      BStar := fun i j _ _ =>
        Real.toNNReal ((1 + (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate) / 2),
      errStar := fun i j _ _ => fun _δ : ℝ => ENNReal.ofReal
        ((Fintype.card (Fin 2) - 1) * (2 ^ (P.varCount i - (j : ℕ)) /
          ((pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate * (Fintype.card F)))),
      C := fun i j => ((pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).C : Set _),
      hcode := fun _ _ => rfl,
      h := ?_,
      hℓ_bound := ?_,
      hℓ_bound' := fun _ _ => by simp,
      hδLe := fun i => le_rfl,
      hlistDecode := ?_ }
  · -- the mutual correlated agreement field, from `mca_rsc_pair_holds`
    intro i j
    letI := inst1 i j
    letI := inst2 i j
    letI := inst3 i j
    letI := inst4 i j
    have hmca := mca_rsc_pair_holds (0 : F) (φ i j) (P.varCount i - (j : ℕ))
      Fin.valEmbedding (hk i j) (fun _ => rfl)
    unfold mca_rsc at hmca
    have h0 : 0 ≤ (1 + (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate) / 2 := by
      have := hrate_nonneg i j
      linarith
    rw [Real.coe_toNNReal _ h0]
    exact hmca
  · -- `|parℓ| = 2` for the generator's own `Fintype` field
    intro i j
    exact Fintype.card_fin 2
  · -- unique decodability at the admissible radius
    intro i j
    letI := inst1 i j
    letI := inst2 i j
    letI := inst3 i j
    letI := inst4 i j
    set ρ : ℝ := (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate with hρ
    -- the chosen radius is below the `j`-th unique-decoding radius
    have hδval : (1 - Finset.univ.sup (fun j : Fin (P.foldingParam i + 1) =>
          Real.toNNReal ((1 + (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate) / 2))
            : ℝ≥0)
        ≤ Real.toNNReal ((1 - ρ) / 2) := by
      refine le_trans (tsub_le_tsub_left (Finset.le_sup (Finset.mem_univ j)) 1) ?_
      rw [tsub_le_iff_right, ← Real.toNNReal_add (by have := hrate_le_one i j; linarith)
        (by have := hrate_nonneg i j; linarith)]
      rw [show (1 - ρ) / 2 + (1 + ρ) / 2 = 1 by ring]
      simp
    have hδR : ((1 - Finset.univ.sup (fun j : Fin (P.foldingParam i + 1) =>
          Real.toNNReal ((1 + (pairUDRGen P S φ inst1 inst2 inst3 inst4 i j).rate) / 2))
            : ℝ≥0) : ℝ)
        ≤ (1 - (2 : ℝ) ^ (P.varCount i - (j : ℕ)) / (@Fintype.card _ (inst1 i j) : ℝ)) / 2 := by
      refine le_trans (NNReal.coe_le_coe.mpr hδval) ?_
      rw [Real.coe_toNNReal _ (by have := hrate_le_one i j; linarith)]
      rw [hρ, hrate i j]
    exact smoothCode_listDecodable_one (φ i j) (P.varCount i - (j : ℕ)) (hk i j) _ hδR

end Instance

end WhirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms WhirIOP.smoothCode_listDecodable_one
#print axioms WhirIOP.genMutualCorrParamsUDR
