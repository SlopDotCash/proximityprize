/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.CapacityBounds
import Mathlib.FieldTheory.Finite.Basic

/-!
# The T4.9.2 bound needs the unique-decoding guard

[BCHKS25, Theorem 1.3] (ABF26 Theorem 4.9 item 2) is stated for fold radii
`γ ∈ [δ/3, δ/2 - 1/n]`, `δ = 1 - k/n`. Without the upper end, the `max{…}/|F|` bound of
`CodingTheory.rs_epsCA_bchks25_item2` is false. This file checks one counterexample, so the
guard `_h_udr` on `rs_epsCA_bchks25_item2` (and on the Issue #87 residual
`bchks25_rs_epsCA_item2_residual`) cannot be dropped.

Instance: `F = L = 𝔽₅` (full domain), `k = 1` (the repetition code, `δ_min = 1`),
`δ_fld = 3/5 > (1 - ρ)/2 = 2/5`, `δ_int = 31/40`. Take the stack `u₀ = x²`, `u₁ = x`.

* Every line point `x² + γ·x` takes some value twice on `𝔽₅`, so it is within distance `3`
  (relative `3/5`) of a constant word.
* The columns `(x², x)` are pairwise distinct, so every pair of constant words misses at least
  `4` columns. The stack is not jointly `31/40`-close (`⌊31/40·5⌋ = 3`).

So `ε_ca(C, 3/5, 31/40) = 1`. The claimed bound is
`max{-1/6, (31/40)/((7/40)·5)} = 31/35 < 1`.
-/

namespace CodingTheory

open ProximityGap NNReal Code

namespace BCHKS25Item2Regime

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The full evaluation domain `𝔽₅ ↪ 𝔽₅`. -/
def dom : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl (ZMod 5)

lemma const_mem (c : ZMod 5) :
    (fun _ : ZMod 5 => c) ∈ (ReedSolomon.code dom 1 : Set (ZMod 5 → ZMod 5)) := by
  refine ⟨Polynomial.C c, ?_, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  · funext x
    simp [ReedSolomon.evalOnPoints]

lemma eq_const_of_mem {w : ZMod 5 → ZMod 5}
    (hw : w ∈ (ReedSolomon.code dom 1 : Set (ZMod 5 → ZMod 5))) :
    w = fun _ => w 0 := by
  obtain ⟨p, hp, rfl⟩ := hw
  rw [SetLike.mem_coe, Polynomial.mem_degreeLT] at hp
  have hpc : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hp)
  funext x
  simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hpc]
  simp

/-- The witness stack `(u₀, u₁) = (x², x)`. -/
def u : Matrix (Fin 2) (ZMod 5) (ZMod 5) := fun j x => if j = 0 then x ^ 2 else x

lemma line_close (γ : ZMod 5) :
    δᵣ(u 0 + γ • u 1, (ReedSolomon.code dom 1 : Set (ZMod 5 → ZMod 5))) ≤ (3 / 5 : ℝ≥0) := by
  rw [relDistFromCode_le_iff_distFromCode_le]
  have h3 : Nat.floor ((3 / 5 : ℝ≥0) * (Fintype.card (ZMod 5) : ℝ≥0)) = 3 := by
    rw [ZMod.card]
    norm_num
  rw [h3, closeToCode_iff_closeToCodeword_of_minDist]
  have key : ∃ c : ZMod 5, hammingDist (u 0 + γ • u 1) (fun _ => c) ≤ 3 := by
    revert γ
    decide
  obtain ⟨c, hc⟩ := key
  exact ⟨_, const_mem c, by exact_mod_cast hc⟩

lemma not_jointProximity :
    ¬ jointProximity (C := (ReedSolomon.code dom 1 : Set (ZMod 5 → ZMod 5))) (u := u)
      (31 / 40 : ℝ≥0) := by
  unfold jointProximity
  intro h
  rw [relDistFromCode_le_iff_distFromCode_le] at h
  have h3 : Nat.floor ((31 / 40 : ℝ≥0) * (Fintype.card (ZMod 5) : ℝ≥0)) = 3 := by
    rw [ZMod.card]
    norm_num [Nat.floor_eq_iff]
  rw [h3, closeToCode_iff_closeToCodeword_of_minDist] at h
  obtain ⟨V, hV, hd⟩ := h
  have h0 := eq_const_of_mem (hV 0)
  have h1 := eq_const_of_mem (hV 1)
  have hVeq : V = fun _ : ZMod 5 => ![V 0 0, V 0 1] := by
    funext x j
    fin_cases j
    · exact congrFun h0 x
    · exact congrFun h1 x
  have hd' : hammingDist (Interleavable.interleave u : Matrix (ZMod 5) (Fin 2) (ZMod 5)) V ≤ 3 := by
    exact_mod_cast hd
  rw [hVeq] at hd'
  have key : ∀ c d : ZMod 5, ¬ hammingDist u.transpose (fun _ : ZMod 5 => ![c, d]) ≤ 3 := by
    decide
  exact key _ _ hd'

lemma one_le_epsCA :
    (1 : ENNReal) ≤ epsCA (F := ZMod 5) (A := ZMod 5)
      (ReedSolomon.code dom 1 : Set (ZMod 5 → ZMod 5)) (3 / 5) (31 / 40) := by
  have := epsCA_ge_card_good_gamma_div_card (F := ZMod 5)
    (ReedSolomon.code dom 1 : Set (ZMod 5 → ZMod 5)) (3 / 5) (31 / 40) u not_jointProximity
    Finset.univ (fun γ _ => line_close γ)
  simpa [Finset.card_univ, ZMod.card, ENNReal.div_self] using this

end BCHKS25Item2Regime

open BCHKS25Item2Regime in
/-- **The unique-decoding guard of T4.9.2 is necessary.** At `F = L = 𝔽₅`, `k = 1`,
`δ_fld = 3/5`, `δ_int = 31/40`, every hypothesis of `rs_epsCA_bchks25_item2` except `_h_udr`
holds, `_h_udr` fails, and the `max{…}/|F|` bound is false (`ε_ca = 1 > 31/35`). -/
theorem rs_epsCA_bchks25_item2_bound_fails_beyond_udr :
    let n : ℝ := Fintype.card (ZMod 5)
    let k : ℕ := 1
    let δ_fld : ℝ≥0 := 3 / 5
    let δ_int : ℝ≥0 := 31 / 40
    let ρ : ℝ := k / n
    (Code.minDist ((ReedSolomon.code dom k : Set (ZMod 5 → ZMod 5))) : ℝ) / n / 3
        ≤ δ_fld ∧
      δ_fld < δ_int ∧
      ¬ ((δ_fld : ℝ) ≤ (1 - ρ) / 2 - 1 / n) ∧
      ¬ epsCA (F := ZMod 5) (A := ZMod 5) ((ReedSolomon.code dom k : Set (ZMod 5 → ZMod 5)))
          δ_fld δ_int ≤
        ENNReal.ofReal
          (max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card (ZMod 5)))
            ((δ_int : ℝ) / ((δ_int - δ_fld) * Fintype.card (ZMod 5)))) := by
  intro n k δ_fld δ_int ρ
  have hn : n = 5 := by simp [n, ZMod.card]
  have hρ : ρ = 1 / 5 := by simp [ρ, k, hn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : Code.minDist ((ReedSolomon.code dom k : Set (ZMod 5 → ZMod 5))) ≤
        Fintype.card (ZMod 5) := by
      rw [← Code.dist_eq_minDist]
      exact Code.dist_le_card _
    rw [ZMod.card] at hle
    have hle' : (Code.minDist ((ReedSolomon.code dom k : Set (ZMod 5 → ZMod 5))) : ℝ) ≤ 5 := by
      exact_mod_cast hle
    rw [hn, div_div, div_le_iff₀ (by norm_num)]
    simp only [δ_fld]
    push_cast
    linarith
  · simp only [δ_fld, δ_int]
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    norm_num
  · rw [hρ, hn]
    simp only [δ_fld]
    push_cast
    norm_num
  · intro h
    have hb := le_trans one_le_epsCA h
    rw [ENNReal.one_le_ofReal, hρ] at hb
    simp only [δ_fld, δ_int, ZMod.card] at hb
    push_cast at hb
    norm_num at hb

end CodingTheory
