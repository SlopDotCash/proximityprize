/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothLadderInstance

/-!
# The monomial strip explosion: `n/(b−1)` bad scalars on the whole staircase strip (#357)

The hypothesis-free, all-scales form of the degenerate-pencil explosion
(`MCAMDSStaircaseRefuted.lean` is the decide-anchored instance).  For the smooth domain
`μ_n = ⟨γ⟩` and any divisor `g ∣ n`, the **telescoping identity**

  `(x^g − c) · ∑_{v < n/g} c^v · x^(n−(v+1)g) = x^n − c^(n/g) = 0`   (`x ∈ μ_n`, `c ∈ μ_(n/g)`)

says the geometric sum `∑_{v<n/g} c^v x^(n−(v+1)g)` vanishes off the fiber
`{x : x^g = c}`.  Reading off its coefficients: the monomial stack

  `u₀ = x^(n−g)`, `u₁ = x^(n−2g)`

has, at the scalar `λ = c`, the **explicit explanation codeword**
`q_c = −∑_{2 ≤ v < n/g} c^v · x^(n−(v+1)g)` (degree `n − 3g < k`) agreeing with the line
on the `≥ n−g`-point witness `S_c = {x : x^g ≠ c}`, while a joint explanation of
`u₁ = x^(n−2g)` (exponent `≥ k`) on `|S_c| ≥ n−g > n−2g` points dies by root counting.
Hence **every** `c ∈ μ_(n/g)` is `mcaEvent`-bad:

  `ε_mca(RS[F, μ_n, k], g/n) ≥ (n/g) / |F|`  whenever  `n − 3g < k ≤ n − 2g`.

In staircase coordinates (`b = g + 1`, band `b`, `d = n − k + 1 ∈ [2b−1, 3b−3]`): the
strip between the `3b−2` collapse threshold and the boundary row explodes to `n/(b−1)`
bad scalars for genuine smooth-domain Reed–Solomon codes — matching the collapse theorem
edge-to-edge (`n − 3g < k` is exactly the complement of `3(b−1) ≤ n − k`), so the two
theorems together totally determine where the RS staircase is linear vs explosive.

No `decide`, no per-instance data: the certificates are closed-form for every scale.
Probe: `probe_mds_pencil_explosion.py` (T1–T6) and the monomial-pair scan at
`(19,18,10)` (the maximizer `(X¹⁵, X¹²)` is this construction at `g = 3`).

## References

Issue #357 (the degenerate-pencil refutation arc); `MCAMDSStaircaseRefuted.lean`,
`SplittingLadder.lean` / `SmoothLadderInstance.lean` (the same telescoping family at the
low-agreement end of the radius axis), `UniversalStaircaseCollapse.lean` /
`MCAStaircaseMaster.lean` (the matching collapse side).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MonomialStripExplosion

open scoped NNReal ENNReal ProbabilityTheory
open Finset Polynomial
open ProximityGap Code
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothLadderInstance

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n g k : ℕ}

section Telescope

/-- **The fiber-complement telescoping identity.**  For `x^n = 1` and `c^(n/g) = 1`
(`g ∣ n`), the geometric sum `∑_{v < n/g} c^v · x^(n−(v+1)g)` is annihilated by
`x^g − c`. -/
theorem telescope_sum_mul (x c : F) (hgn : g ∣ n) (hg1 : 1 ≤ g)
    (hx : x ^ n = 1) (hc : c ^ (n / g) = 1) :
    (∑ v ∈ Finset.range (n / g), c ^ v * x ^ (n - (v + 1) * g)) * (x ^ g - c) = 0 := by
  have hGg : g * (n / g) = n := Nat.mul_div_cancel' hgn
  have hGg' : (n / g) * g = n := by rw [Nat.mul_comm]; exact hGg
  have hsum : ∑ v ∈ Finset.range (n / g),
      (c ^ v * x ^ (n - v * g) - c ^ (v + 1) * x ^ (n - (v + 1) * g))
      = c ^ 0 * x ^ (n - 0 * g) - c ^ (n / g) * x ^ (n - (n / g) * g) :=
    Finset.sum_range_sub' (fun v => c ^ v * x ^ (n - v * g)) (n / g)
  have hterm : ∀ v ∈ Finset.range (n / g),
      c ^ v * x ^ (n - (v + 1) * g) * (x ^ g - c)
        = c ^ v * x ^ (n - v * g) - c ^ (v + 1) * x ^ (n - (v + 1) * g) := by
    intro v hv
    have hvG : v < n / g := Finset.mem_range.mp hv
    have hle : (v + 1) * g ≤ n := by
      calc (v + 1) * g ≤ (n / g) * g := Nat.mul_le_mul_right g hvG
        _ = n := hGg'
    have hexp : n - (v + 1) * g + g = n - v * g := by
      have hvg : v * g + g = (v + 1) * g := by ring
      omega
    rw [mul_sub]
    congr 1
    · rw [mul_assoc, ← pow_add, hexp]
    · rw [pow_succ]
      ring
  rw [Finset.sum_mul, Finset.sum_congr rfl hterm, hsum]
  have hzero : n - (n / g) * g = 0 := by omega
  rw [pow_zero, one_mul, Nat.zero_mul, Nat.sub_zero, hx, hzero, pow_zero, mul_one, hc,
    sub_self]

/-- Off the fiber (`x^g ≠ c`), the geometric sum vanishes. -/
theorem telescope_sum_eq_zero (x c : F) (hgn : g ∣ n) (hg1 : 1 ≤ g)
    (hx : x ^ n = 1) (hc : c ^ (n / g) = 1) (hxc : ¬ x ^ g = c) :
    ∑ v ∈ Finset.range (n / g), c ^ v * x ^ (n - (v + 1) * g) = 0 := by
  rcases mul_eq_zero.mp (telescope_sum_mul x c hgn hg1 hx hc) with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hxc

end Telescope

section Strip

variable (γ : F)

/-- The explanation codeword for the scalar `c`: the tail of the geometric sum has
degree `n − 3g < k`. -/
theorem explanation_mem (c : F) (hk_lo : n - 3 * g < k) :
    (fun i : Fin n => -(∑ v ∈ Finset.Ico 2 (n / g),
      c ^ v * smoothDom γ n i ^ (n - (v + 1) * g)))
      ∈ (evalCode (smoothDom γ n) k : Set (Fin n → F)) := by
  refine ⟨-(∑ v ∈ Finset.Ico 2 (n / g), Polynomial.C (c ^ v) * X ^ (n - (v + 1) * g)),
    ?_, ?_⟩
  · rw [Polynomial.natDegree_neg]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro v hv
    have hv2 : 2 ≤ v := (Finset.mem_Ico.mp hv).1
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    have h3g : 3 * g ≤ (v + 1) * g := Nat.mul_le_mul_right g (by omega)
    omega
  · intro i
    simp only [Polynomial.eval_neg, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The fiber `{i : dom i ^ g = c}` has at most `g` elements (roots of `X^g − c`). -/
theorem fiber_card_le (dom : Fin n → F) (hinj : Function.Injective dom)
    (c : F) (hg1 : 1 ≤ g) :
    (Finset.univ.filter (fun i : Fin n => dom i ^ g = c)).card ≤ g := by
  classical
  have hne : (X ^ g - Polynomial.C c : Polynomial F) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by omega) c
  have hsub : (Finset.univ.filter (fun i : Fin n => dom i ^ g = c)).image dom
      ⊆ (X ^ g - Polynomial.C c : Polynomial F).roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    show Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, (Finset.mem_filter.mp hi).2, sub_self]
  calc (Finset.univ.filter (fun i : Fin n => dom i ^ g = c)).card
      = ((Finset.univ.filter (fun i : Fin n => dom i ^ g = c)).image dom).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (X ^ g - Polynomial.C c : Polynomial F).roots.toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ Multiset.card (X ^ g - Polynomial.C c : Polynomial F).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (X ^ g - Polynomial.C c : Polynomial F).natDegree :=
        Polynomial.card_roots' _
    _ ≤ g := by rw [Polynomial.natDegree_X_pow_sub_C]

open Classical in
/-- **The strip event.**  For `μ_n = ⟨γ⟩`, `g ∣ n`, `n − 3g < k ≤ n − 2g`: every
`c ∈ μ_(n/g)` is `mcaEvent`-bad for the stack `(x^(n−g), x^(n−2g))` at radius `g/n`. -/
theorem strip_mcaEvent [Nonempty (Fin n)] (hord : orderOf γ = n) (hg1 : 1 ≤ g)
    (hgn : g ∣ n) (hk_lo : n - 3 * g < k) (hk_hi : k ≤ n - 2 * g) (hn2g : 2 * g < n)
    (c : F) (hc : c ^ (n / g) = 1) :
    mcaEvent (F := F) (A := F) (evalCode (smoothDom γ n) k : Set (Fin n → F))
      ((g : ℝ≥0) / (n : ℝ≥0))
      (fun i => smoothDom γ n i ^ (n - g))
      (fun i => smoothDom γ n i ^ (n - 2 * g)) c := by
  have hinj : Function.Injective (smoothDom γ n) := smoothDom_injective γ hord
  have hGg : g * (n / g) = n := Nat.mul_div_cancel' hgn
  have hG2 : 2 ≤ n / g := (Nat.le_div_iff_mul_le (by omega : 0 < g)).mpr (by omega)
  have hγn : γ ^ n = 1 := by
    conv_lhs => rw [← hord]
    exact pow_orderOf_eq_one γ
  have hxn : ∀ i : Fin n, smoothDom γ n i ^ n = 1 := by
    intro i
    unfold smoothDom
    rw [← pow_mul, mul_comm (i : ℕ) n, pow_mul, hγn, one_pow]
  -- the witness: complement of the fiber
  set S : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => ¬ smoothDom γ n i ^ g = c) with hS
  have hcompl : S = Finset.univ \
      (Finset.univ.filter (fun i : Fin n => smoothDom γ n i ^ g = c)) := by
    ext i
    simp [hS]
  have hScard : n - g ≤ S.card := by
    have hfib := fiber_card_le (g := g) (smoothDom γ n) hinj c hg1
    have hcard : S.card = n -
        (Finset.univ.filter (fun i : Fin n => smoothDom γ n i ^ g = c)).card := by
      rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
    omega
  refine ⟨S, ?_, ⟨_, explanation_mem γ c hk_lo, ?_⟩, ?_⟩
  · -- size clause: |S| ≥ (1 − g/n)·n = n − g
    have hnpos : 0 < n := by omega
    have hgn' : (g : ℝ≥0) / n ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hnpos : (0 : ℝ≥0) < (n : ℝ≥0))]
      exact_mod_cast (by omega : g ≤ n)
    simp only [Fintype.card_fin, ge_iff_le]
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hgn']
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hn0)]
    have h1 : ((n - g : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hScard
    have h2 : ((n - g : ℕ) : ℝ) = (n : ℝ) - g := by
      push_cast [Nat.cast_sub (by omega : g ≤ n)]
      ring
    linarith
  · -- agreement: the explanation equals the line on S
    intro i hi
    have hxc : ¬ smoothDom γ n i ^ g = c := by
      have hmem := hi
      rw [hS] at hmem
      exact (Finset.mem_filter.mp hmem).2
    have htel := telescope_sum_eq_zero (g := g) (n := n) (smoothDom γ n i) c hgn hg1
      (hxn i) hc hxc
    have hsplit : ∑ v ∈ Finset.range (n / g),
        c ^ v * smoothDom γ n i ^ (n - (v + 1) * g)
        = smoothDom γ n i ^ (n - g) + c * smoothDom γ n i ^ (n - 2 * g)
          + ∑ v ∈ Finset.Ico 2 (n / g),
              c ^ v * smoothDom γ n i ^ (n - (v + 1) * g) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2) hG2]
      congr 1
      rw [← Finset.range_eq_Ico, Finset.sum_range_succ, Finset.sum_range_one]
      have e0 : n - (0 + 1) * g = n - g := by omega
      have e1 : n - (1 + 1) * g = n - 2 * g := by omega
      rw [e0, e1, pow_zero, one_mul, pow_one]
    rw [hsplit] at htel
    show -(∑ v ∈ Finset.Ico 2 (n / g), c ^ v * smoothDom γ n i ^ (n - (v + 1) * g))
        = smoothDom γ n i ^ (n - g) + c • smoothDom γ n i ^ (n - 2 * g)
    rw [smul_eq_mul]
    linear_combination -htel
  · -- no joint explanation: u₁ = x^(n−2g) is uninterpolable on ≥ n−g points
    rintro ⟨v₀, _, v₁, hv₁, hag⟩
    obtain ⟨P, hPdeg, hPv⟩ := hv₁
    have hk1 : 1 ≤ k := by omega
    set D : Polynomial F := X ^ (n - 2 * g) - P with hD
    have hdegP : P.degree < ((n - 2 * g : ℕ) : WithBot ℕ) := by
      calc P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ ((k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hPdeg
        _ < ((n - 2 * g : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : k - 1 < n - 2 * g)
    have hDdeg : D.degree = ((n - 2 * g : ℕ) : WithBot ℕ) := by
      rw [hD, Polynomial.degree_sub_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hdegP), Polynomial.degree_X_pow]
    have hDne : D ≠ 0 := by
      intro h
      rw [h, Polynomial.degree_zero] at hDdeg
      exact absurd hDdeg.symm (by simp)
    have hDz : D = 0 := by
      refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
        (f := D) (s := S.image (smoothDom γ n)) ?_ ?_
      · calc D.degree = ((n - 2 * g : ℕ) : WithBot ℕ) := hDdeg
          _ < ((n - g : ℕ) : WithBot ℕ) := by
              exact_mod_cast (by omega : n - 2 * g < n - g)
          _ ≤ (((S.image (smoothDom γ n)).card : ℕ) : WithBot ℕ) := by
              rw [Finset.card_image_of_injective _ hinj]
              exact_mod_cast hScard
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        rw [hD, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
        have h1 : v₁ i = P.eval (smoothDom γ n i) := hPv i
        have h2 : v₁ i = smoothDom γ n i ^ (n - 2 * g) := (hag i hi).2
        rw [← h1, h2, sub_self]
    exact hDne hDz

open Classical in
/-- **THE MONOMIAL STRIP EXPLOSION.**  For the smooth domain `μ_n = ⟨γ⟩` and any
divisor `g ∣ n` with `n − 3g < k ≤ n − 2g` (i.e. distance `d = n − k + 1` in the strip
`(2g, 3g]`, band `b = g + 1`):

  `ε_mca(RS[F, μ_n, k], g/n) ≥ (n/g) / |F|`.

In staircase terms: on every band `b` with distance `2b − 1 ≤ d ≤ 3b − 3`, smooth-domain
RS explodes to `n/(b−1)` bad scalars — the `3b−2` collapse threshold
(`UniversalStaircaseCollapse` / `MCAStaircaseMaster`) is sharp for Reed–Solomon codes,
with the two theorems meeting edge-to-edge (`n − 3g < k` ⟺ `¬(3(b−1) ≤ n − k)`). -/
theorem strip_eps_ge [Nonempty (Fin n)] (hord : orderOf γ = n) (hg1 : 1 ≤ g)
    (hgn : g ∣ n) (hk_lo : n - 3 * g < k) (hk_hi : k ≤ n - 2 * g) (hn2g : 2 * g < n) :
    ((n / g : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (evalCode (smoothDom γ n) k : Set (Fin n → F))
          ((g : ℝ≥0) / (n : ℝ≥0)) := by
  have hordg : orderOf (γ ^ g) = n / g := by
    rw [orderOf_pow' γ (by omega : g ≠ 0), hord, Nat.gcd_eq_right hgn]
  set lams : Fin (n / g) → F := fun j => (γ ^ g) ^ (j : ℕ) with hlams
  have hlinj : Function.Injective lams := by
    intro a b hab
    have h := pow_injOn_Iio_orderOf (x := γ ^ g)
      (by rw [hordg]; exact Set.mem_Iio.mpr a.isLt)
      (by rw [hordg]; exact Set.mem_Iio.mpr b.isLt) hab
    exact Fin.ext h
  have hG := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (evalCode (smoothDom γ n) k : Set (Fin n → F)) ((g : ℝ≥0) / (n : ℝ≥0))
    ![fun i => smoothDom γ n i ^ (n - g), fun i => smoothDom γ n i ^ (n - 2 * g)]
    (Finset.univ.image lams) ?_
  · rwa [Finset.card_image_of_injective _ hlinj, Finset.card_univ,
      Fintype.card_fin] at hG
  · intro c hcmem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hcmem
    have hgg1 : (γ ^ g) ^ (n / g) = 1 := by
      conv_lhs => rw [← hordg]
      exact pow_orderOf_eq_one _
    have hc : lams j ^ (n / g) = 1 := by
      show ((γ ^ g) ^ (j : ℕ)) ^ (n / g) = 1
      rw [← pow_mul, mul_comm (j : ℕ) (n / g), pow_mul, hgg1, one_pow]
    have := strip_mcaEvent (g := g) (k := k) γ hord hg1 hgn hk_lo hk_hi hn2g
      (lams j) hc
    simpa using this

end Strip

end ProximityGap.MonomialStripExplosion

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialStripExplosion.telescope_sum_eq_zero
#print axioms ProximityGap.MonomialStripExplosion.strip_mcaEvent
#print axioms ProximityGap.MonomialStripExplosion.strip_eps_ge
