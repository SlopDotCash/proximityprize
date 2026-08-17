/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialStripExplosion
import ArkLib.Data.CodingTheory.ProximityGap.StripEdgeDeltaStar

/-!
# The coset-clique boundary law: `ε_mca ≥ n/|F|` on the rows below the strip (#357)

The closed-form theorem behind the boundary-row probes (`probe_band4_boundary_coset_cliques`,
`probe_boundary_n12_coset_triangles`) and the O148 registered target ("γ is bad iff the
line factor `X + γ` has a root in the evaluation domain").  For the monomial stack

  `u₀ = x^(n−b+1)`, `u₁ = x^(n−b)`     (line `= x^(n−b)·(x + γ)`)

over the smooth domain `μ_n = ⟨ζ⟩` with `b ∣ n`, every `γ ∈ −μ_n` is `mcaEvent`-bad at
radius `(b−1)/n`: writing `x* = −γ` and `c = x*^b ∈ μ_(n/b)`, the **twisted telescoping
identity**

  `x^b·q(x) = −c·(x − x*)·G(x) + (x + γ)`,
  `G(x) = ∑_{v<N} c^v x^((N−1−v)b)` (so `(x^b − c)·G = x^n − c^N = 0` on `μ_n`),
  `q(x) = −∑_{v<N−1} c^(v+1)·(x^((N−2−v)b+1) − x*·x^((N−2−v)b))`,   `N = n/b`

exhibits the **explicit degree-`(n−2b+1)` explanation codeword** `q` agreeing with the
line on the `(n−b+1)`-point witness `{x : x^b ≠ c} ∪ {x*}` (the complement of `b−1`
points of the `μ_b`-coset of `x*`), while a joint explanation of `u₁ = x^(n−b)` dies by
root counting whenever `k ≤ n − b`.  Hence for all `n − 2b + 2 ≤ k ≤ n − b`
(distance `d = n − k + 1 ∈ [b+1, 2b−1]` — the rows from the band edge down to and
including the boundary row):

  **`ε_mca(RS[F, μ_n, k], (b−1)/n) ≥ n/|F|`** — flat-`n`, field-independent numerator.

This is the syndrome-space coset-clique alignment of the probes (the common 2-plane of
the `μ_b`-coset-clique spans is exactly the `(G, x·G)`-fraction plane), the `≥` half of
the O148 law `excess census = −domain`, and — at 2-power `n` where every 2-power `b`
divides `n` — the reason the production staircase carries `~n/q` mass at every boundary
row `d = 2b − 1`, `b ∈ {2, 4, 8, …}`.

## References

Issue #357 (the boundary-row incidence arc); `MonomialStripExplosion.lean` (the same
telescoping one row up, whose `g = b − 1` pencil this strictly beats at the boundary),
`CosetSplittingFloor.lean` (the `b = n/2` instance), DISPROOF_LOG O147/O148.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.CosetCliqueBoundary

open scoped NNReal ENNReal ProbabilityTheory
open Finset Polynomial
open ProximityGap Code
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothLadderInstance
open ProximityGap.MonomialStripExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n b k : ℕ}

section Telescope

/-- The ascending telescoping polynomial `G(x) = ∑_{v<N} c^v·x^((N−1−v)b)`:
`(x^b − c)·G(x) = x^(Nb) − c^N`. -/
theorem clique_telescope (x c : F) (N : ℕ) (hb : 1 ≤ b) :
    (∑ v ∈ Finset.range N, c ^ v * x ^ ((N - 1 - v) * b)) * (x ^ b - c)
      = x ^ (N * b) - c ^ N := by
  have hsum : ∑ v ∈ Finset.range N,
      (c ^ v * x ^ ((N - v) * b) - c ^ (v + 1) * x ^ ((N - (v + 1)) * b))
      = c ^ 0 * x ^ ((N - 0) * b) - c ^ N * x ^ ((N - N) * b) :=
    Finset.sum_range_sub' (fun v => c ^ v * x ^ ((N - v) * b)) N
  have hterm : ∀ v ∈ Finset.range N,
      c ^ v * x ^ ((N - 1 - v) * b) * (x ^ b - c)
        = c ^ v * x ^ ((N - v) * b) - c ^ (v + 1) * x ^ ((N - (v + 1)) * b) := by
    intro v hv
    have hvN : v < N := Finset.mem_range.mp hv
    have hexp : (N - 1 - v) * b + b = (N - v) * b := by
      have h1 : N - 1 - v + 1 = N - v := by omega
      calc (N - 1 - v) * b + b = (N - 1 - v + 1) * b := by ring
        _ = (N - v) * b := by rw [h1]
    have hexp2 : N - (v + 1) = N - 1 - v := by omega
    rw [mul_sub, hexp2]
    congr 1
    · rw [mul_assoc, ← pow_add, hexp]
    · rw [pow_succ]
      ring
  rw [Finset.sum_mul, Finset.sum_congr rfl hterm, hsum]
  rw [pow_zero, one_mul, Nat.sub_zero, Nat.sub_self, Nat.zero_mul, pow_zero, mul_one]

end Telescope

section Boundary

variable (ζ : F)

/-- The explicit explanation word for the scalar `γ = −x*`:
`q(x) = −∑_{v<N−1} c^(v+1)·(x^((N−2−v)b+1) − x*·x^((N−2−v)b))`, degree `≤ n − 2b + 1`. -/
theorem clique_explanation_mem (c xstar : F) (hbn : b ∣ n) (hb2 : 2 ≤ b)
    (hk_lo : n - 2 * b + 2 ≤ k) (hbn2 : 2 * b ≤ n) :
    (fun i : Fin n => -(∑ v ∈ Finset.range (n / b - 1),
      c ^ (v + 1) * (smoothDom ζ n i ^ ((n / b - 2 - v) * b + 1)
        - xstar * smoothDom ζ n i ^ ((n / b - 2 - v) * b))))
      ∈ (evalCode (smoothDom ζ n) k : Set (Fin n → F)) := by
  have hGg : b * (n / b) = n := Nat.mul_div_cancel' hbn
  refine ⟨-(∑ v ∈ Finset.range (n / b - 1),
    Polynomial.C (c ^ (v + 1)) * (X ^ ((n / b - 2 - v) * b + 1)
      - Polynomial.C xstar * X ^ ((n / b - 2 - v) * b))), ?_, ?_⟩
  · rw [Polynomial.natDegree_neg]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro v hv
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    have h2 : (Polynomial.C xstar * X ^ ((n / b - 2 - v) * b)).natDegree
        ≤ (n / b - 2 - v) * b := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_X_pow]
    have hle : (n / b - 2 - v) * b + 1 ≤ n - 2 * b + 1 := by
      have hNb : (n / b - 2 - v) * b ≤ (n / b - 2) * b :=
        Nat.mul_le_mul_right b (by omega)
      have h2b : (n / b - 2) * b = n - 2 * b := by
        have hN2 : 2 ≤ n / b := (Nat.le_div_iff_mul_le (by omega : 0 < b)).mpr (by omega)
        have : (n / b - 2) * b + 2 * b = n := by
          have := hGg
          calc (n / b - 2) * b + 2 * b = (n / b - 2 + 2) * b := by ring
            _ = (n / b) * b := by congr 1; omega
            _ = n := by rw [Nat.mul_comm]; exact hGg
        omega
      omega
    refine max_le (by omega) (le_trans h2 (by omega))
  · intro i
    simp only [Polynomial.eval_neg, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

open Classical in
/-- **The boundary event.**  For `μ_n = ⟨ζ⟩`, `b ∣ n`, `2 ≤ b`, `2b < n`,
`n − 2b + 2 ≤ k ≤ n − b`: every `γ = −x*` with `x* ∈ μ_n` is `mcaEvent`-bad for the
stack `(x^(n−b+1), x^(n−b))` at radius `(b−1)/n`. -/
theorem clique_mcaEvent [Nonempty (Fin n)] (hord : orderOf ζ = n) (hb2 : 2 ≤ b)
    (hbn : b ∣ n) (hk_lo : n - 2 * b + 2 ≤ k) (hk_hi : k ≤ n - b) (hbn2 : 2 * b < n)
    (istar : Fin n) :
    mcaEvent (F := F) (A := F) (evalCode (smoothDom ζ n) k : Set (Fin n → F))
      (((b : ℝ≥0) - 1) / (n : ℝ≥0))
      (fun i => smoothDom ζ n i ^ (n - b + 1))
      (fun i => smoothDom ζ n i ^ (n - b)) (-(smoothDom ζ n istar)) := by
  have hinj : Function.Injective (smoothDom ζ n) := smoothDom_injective ζ hord
  have hGg : b * (n / b) = n := Nat.mul_div_cancel' hbn
  set N : ℕ := n / b with hN
  have hN2 : 2 ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < b)).mpr (by omega)
  set xstar : F := smoothDom ζ n istar with hxstar
  set c : F := xstar ^ b with hc
  have hxn : ∀ i : Fin n, smoothDom ζ n i ^ n = 1 := by
    intro i
    have hζn : ζ ^ n = 1 := by
      conv_lhs => rw [← hord]
      exact pow_orderOf_eq_one ζ
    unfold smoothDom
    rw [← pow_mul, mul_comm (i : ℕ) n, pow_mul, hζn, one_pow]
  have hxne : ∀ i : Fin n, smoothDom ζ n i ≠ 0 := by
    intro i hzero
    have := hxn i
    rw [hzero, zero_pow (by omega : n ≠ 0)] at this
    exact zero_ne_one this
  have hcN : c ^ N = 1 := by
    rw [hc, ← pow_mul, hGg]
    exact hxn istar
  -- the witness: complement of the fiber, plus the crossing point
  set S : Finset (Fin n) :=
    insert istar (Finset.univ.filter (fun i : Fin n => ¬ smoothDom ζ n i ^ b = c))
      with hS
  have histar_not : istar ∉
      Finset.univ.filter (fun i : Fin n => ¬ smoothDom ζ n i ^ b = c) := by
    simp [hc, hxstar]
  have hScard : n - b + 1 ≤ S.card := by
    rw [hS, Finset.card_insert_of_notMem histar_not]
    have hfib := fiber_card_le (g := b) (smoothDom ζ n) hinj c (by omega)
    have hcompl : (Finset.univ.filter
        (fun i : Fin n => ¬ smoothDom ζ n i ^ b = c)).card = n -
        (Finset.univ.filter (fun i : Fin n => smoothDom ζ n i ^ b = c)).card := by
      have : (Finset.univ.filter (fun i : Fin n => ¬ smoothDom ζ n i ^ b = c))
          = Finset.univ \
            (Finset.univ.filter (fun i : Fin n => smoothDom ζ n i ^ b = c)) := by
        ext i
        simp
      rw [this, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  -- the explanation word
  set qw : Fin n → F := fun i => -(∑ v ∈ Finset.range (N - 1),
    c ^ (v + 1) * (smoothDom ζ n i ^ ((N - 2 - v) * b + 1)
      - xstar * smoothDom ζ n i ^ ((N - 2 - v) * b))) with hqw
  -- the master pointwise identity: x^b·qw(x) = −c(x − x*)G(x) + (x + γ), γ = −x*
  have hmaster : ∀ i : Fin n,
      smoothDom ζ n i ^ b * qw i
        = -(c * (smoothDom ζ n i - xstar)
            * (∑ v ∈ Finset.range N, c ^ v * smoothDom ζ n i ^ ((N - 1 - v) * b)))
          + (smoothDom ζ n i - xstar) := by
    intro i
    set x : F := smoothDom ζ n i with hx
    have hqi : qw i = -(∑ v ∈ Finset.range (N - 1),
        c ^ (v + 1) * (x ^ ((N - 2 - v) * b + 1) - xstar * x ^ ((N - 2 - v) * b))) := rfl
    have hsplit : c * (x - xstar)
        * (∑ v ∈ Finset.range N, c ^ v * x ^ ((N - 1 - v) * b))
        = (∑ v ∈ Finset.range (N - 1),
            c ^ (v + 1) * (x ^ ((N - 1 - v) * b + 1) - xstar * x ^ ((N - 1 - v) * b)))
          + c ^ N * (x - xstar) := by
      have hNsucc : N = (N - 1) + 1 := by omega
      rw [Finset.mul_sum]
      have hterm : ∀ v ∈ Finset.range N,
          c * (x - xstar) * (c ^ v * x ^ ((N - 1 - v) * b))
            = c ^ (v + 1) * (x ^ ((N - 1 - v) * b + 1) - xstar * x ^ ((N - 1 - v) * b)) := by
        intro v _
        ring
      rw [Finset.sum_congr rfl hterm]
      conv_lhs => rw [hNsucc, Finset.sum_range_succ]
      congr 1
      have hlast : N - 1 + 1 - 1 - (N - 1) = 0 := by omega
      have hcsucc : c ^ (N - 1 + 1) = c ^ N := by
        congr 1
        omega
      rw [hlast, Nat.zero_mul, pow_zero, mul_one, pow_one, hcsucc]
    have hqterm : x ^ b * qw i
        = -(∑ v ∈ Finset.range (N - 1),
            c ^ (v + 1) * (x ^ ((N - 1 - v) * b + 1) - xstar * x ^ ((N - 1 - v) * b))) := by
      rw [hqi, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvN : v < N - 1 := Finset.mem_range.mp hv
      have he1 : x ^ ((N - 1 - v) * b + 1) = x ^ ((N - 2 - v) * b + 1) * x ^ b := by
        rw [← pow_add]
        congr 1
        have : N - 2 - v + 1 = N - 1 - v := by omega
        calc (N - 1 - v) * b + 1 = (N - 2 - v + 1) * b + 1 := by rw [this]
          _ = (N - 2 - v) * b + 1 + b := by ring
      have he0 : x ^ ((N - 1 - v) * b) = x ^ ((N - 2 - v) * b) * x ^ b := by
        rw [← pow_add]
        congr 1
        have : N - 2 - v + 1 = N - 1 - v := by omega
        calc (N - 1 - v) * b = (N - 2 - v + 1) * b := by rw [this]
          _ = (N - 2 - v) * b + b := by ring
      rw [he1, he0]
      ring
    have hsplit' : (∑ v ∈ Finset.range (N - 1),
        c ^ (v + 1) * (x ^ ((N - 1 - v) * b + 1) - xstar * x ^ ((N - 1 - v) * b)))
        = c * (x - xstar) * (∑ v ∈ Finset.range N, c ^ v * x ^ ((N - 1 - v) * b))
          - (x - xstar) := by
      rw [hsplit, hcN]
      ring
    rw [hqterm, hsplit']
    ring
  refine ⟨S, ?_, ⟨qw, clique_explanation_mem ζ c xstar hbn hb2 hk_lo (by omega), ?_⟩, ?_⟩
  · -- size clause: |S| ≥ (1 − (b−1)/n)·n = n − b + 1
    have hnpos : 0 < n := by omega
    have hb1n : ((b : ℝ≥0) - 1) / n ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hnpos : (0 : ℝ≥0) < (n : ℝ≥0))]
      calc (b : ℝ≥0) - 1 ≤ (b : ℝ≥0) := tsub_le_self
        _ ≤ (n : ℝ≥0) := by exact_mod_cast (by omega : b ≤ n)
    simp only [Fintype.card_fin, ge_iff_le]
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hb1n, NNReal.coe_sub (by exact_mod_cast (by omega : 1 ≤ b) : (1 : ℝ≥0) ≤ (b : ℝ≥0))]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hn0)]
    have h1 : ((n - b + 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hScard
    have h2 : ((n - b + 1 : ℕ) : ℝ) = (n : ℝ) - ((b : ℝ) - 1) := by
      push_cast [Nat.cast_sub (by omega : b ≤ n)]
      ring
    linarith
  · -- agreement on S
    intro i hi
    set x : F := smoothDom ζ n i with hx
    have hgoal : qw i = x ^ (n - b + 1) + (-(xstar)) • x ^ (n - b) := by
      have hxbq := hmaster i
      rw [← hx] at hxbq
      have hcase : x = xstar ∨ ¬ x ^ b = c := by
        rw [hS] at hi
        rcases Finset.mem_insert.mp hi with h | h
        · left
          rw [hx, h]
        · right
          exact (Finset.mem_filter.mp h).2
      have hzero : x ^ b * qw i = x - xstar := by
        rcases hcase with heq | hne
        · -- x = x*: both the G-term and (x − x*) vanish
          rw [hxbq, heq]
          ring
        · -- off the fiber: G(x) = 0
          have hGzero : (∑ v ∈ Finset.range N, c ^ v * x ^ ((N - 1 - v) * b)) = 0 := by
            have htel := clique_telescope (b := b) x c N (by omega)
            rw [hN] at htel ⊢
            have hxNb : x ^ ((n / b) * b) = 1 := by
              rw [Nat.mul_comm, hGg]
              exact hxn i
            rw [hxNb, hcN] at htel
            rw [sub_self] at htel
            rcases mul_eq_zero.mp htel with h | h
            · exact h
            · exact absurd (sub_eq_zero.mp h) hne
          rw [hxbq, hGzero]
          ring
      -- multiply by x^(n−b): x^n = 1
      have hxb_ne : x ^ b ≠ 0 := pow_ne_zero b (by rw [hx]; exact hxne i)
      have hkey : x ^ (n - b) * (x ^ b * qw i) = x ^ (n - b) * (x - xstar) := by
        rw [hzero]
      have hxnb : x ^ (n - b) * x ^ b = 1 := by
        rw [← pow_add]
        have : n - b + b = n := by omega
        rw [this, hx]
        exact hxn i
      have hq : qw i = x ^ (n - b) * (x - xstar) := by
        calc qw i = (x ^ (n - b) * x ^ b) * qw i := by rw [hxnb, one_mul]
          _ = x ^ (n - b) * (x ^ b * qw i) := by ring
          _ = x ^ (n - b) * (x - xstar) := hkey
      rw [hq, smul_eq_mul]
      have : x ^ (n - b) * x = x ^ (n - b + 1) := by
        rw [pow_succ]
      calc x ^ (n - b) * (x - xstar) = x ^ (n - b) * x - xstar * x ^ (n - b) := by ring
        _ = x ^ (n - b + 1) + -xstar * x ^ (n - b) := by rw [this]; ring
    exact hgoal
  · -- no joint explanation: u₁ = x^(n−b) is uninterpolable on ≥ n−b+1 points
    rintro ⟨v₀, _, v₁, hv₁, hag⟩
    obtain ⟨P, hPdeg, hPv⟩ := hv₁
    have hk1 : 1 ≤ k := by omega
    set D : Polynomial F := X ^ (n - b) - P with hD
    have hdegP : P.degree < ((n - b : ℕ) : WithBot ℕ) := by
      calc P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ ((k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hPdeg
        _ < ((n - b : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : k - 1 < n - b)
    have hDdeg : D.degree = ((n - b : ℕ) : WithBot ℕ) := by
      rw [hD, Polynomial.degree_sub_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hdegP), Polynomial.degree_X_pow]
    have hDne : D ≠ 0 := by
      intro h
      rw [h, Polynomial.degree_zero] at hDdeg
      exact absurd hDdeg.symm (by simp)
    have hDz : D = 0 := by
      refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
        (f := D) (s := S.image (smoothDom ζ n)) ?_ ?_
      · calc D.degree = ((n - b : ℕ) : WithBot ℕ) := hDdeg
          _ < ((n - b + 1 : ℕ) : WithBot ℕ) := by
              exact_mod_cast (by omega : n - b < n - b + 1)
          _ ≤ (((S.image (smoothDom ζ n)).card : ℕ) : WithBot ℕ) := by
              rw [Finset.card_image_of_injective _ hinj]
              exact_mod_cast hScard
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        rw [hD, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
        have h1 : v₁ i = P.eval (smoothDom ζ n i) := hPv i
        have h2 : v₁ i = smoothDom ζ n i ^ (n - b) := (hag i hi).2
        rw [← h1, h2, sub_self]
    exact hDne hDz

open Classical in
/-- **THE COSET-CLIQUE BOUNDARY LAW.**  For `μ_n = ⟨ζ⟩`, `b ∣ n`, `2 ≤ b`, `2b < n`,
and every dimension `n − 2b + 2 ≤ k ≤ n − b` (distance `d = n − k + 1 ∈ [b+1, 2b−1]`,
covering the boundary row `d = 2b − 1` and every row down to the band edge):

  `ε_mca(RS[F, μ_n, k], (b−1)/n) ≥ n/|F|` — the flat-`n` law, every scale, closed form.

The bad set is exactly `−μ_n` ⊆ bad (the ≥ half of the O148 law: `γ` is bad whenever
the line factor `X + γ` has a root in the domain). -/
theorem clique_eps_ge [Nonempty (Fin n)] (hord : orderOf ζ = n) (hb2 : 2 ≤ b)
    (hbn : b ∣ n) (hk_lo : n - 2 * b + 2 ≤ k) (hk_hi : k ≤ n - b) (hbn2 : 2 * b < n) :
    ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (evalCode (smoothDom ζ n) k : Set (Fin n → F))
          (((b : ℝ≥0) - 1) / (n : ℝ≥0)) := by
  have hinj : Function.Injective (smoothDom ζ n) := smoothDom_injective ζ hord
  set lams : Fin n → F := fun j => -(smoothDom ζ n j) with hlams
  have hlinj : Function.Injective lams := by
    intro a b' hab
    exact hinj (neg_injective hab)
  have hG := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (evalCode (smoothDom ζ n) k : Set (Fin n → F)) (((b : ℝ≥0) - 1) / (n : ℝ≥0))
    ![fun i => smoothDom ζ n i ^ (n - b + 1), fun i => smoothDom ζ n i ^ (n - b)]
    (Finset.univ.image lams) ?_
  · rwa [Finset.card_image_of_injective _ hlinj, Finset.card_univ,
      Fintype.card_fin] at hG
  · intro γ hγmem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hγmem
    have := clique_mcaEvent (k := k) ζ hord hb2 hbn hk_lo hk_hi hbn2 j
    simpa using this

open Classical in
/-- **The divisor-family δ\* cap.**  Whenever `ε* < n/|F|` (under-sized fields:
`|F| < n·2¹²⁸` at the prize target), the boundary law caps the threshold at *every*
divisor radius: `δ*(RS[F, μ_n, k], ε*) ≤ (b−1)/n` for each `b ∣ n` with
`n − 2b + 2 ≤ k ≤ n − b`.  The binding cap is the smallest admissible divisor
`b ≥ (n − k + 1)/2`; this extends `mcaDeltaStar_le_of_undersized_field` (the `b = n/2`
half-pair radius) to the whole divisor family — at 2-power `n` the caps recur at every
2-power band, which is where the prize's large-field hypothesis is consumed. -/
theorem mcaDeltaStar_le_of_undersized_boundary [Nonempty (Fin n)]
    (hord : orderOf ζ = n) (hb2 : 2 ≤ b)
    (hbn : b ∣ n) (hk_lo : n - 2 * b + 2 ≤ k) (hk_hi : k ≤ n - b) (hbn2 : 2 * b < n)
    {εstar : ℝ≥0∞} (hε : εstar < ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      (evalCode (smoothDom ζ n) k : Set (Fin n → F)) εstar
      ≤ ((b : ℝ≥0) - 1) / (n : ℝ≥0) :=
  MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hε (clique_eps_ge ζ hord hb2 hbn hk_lo hk_hi hbn2))

open Classical in
/-- **Exact δ\* at the boundary-row codes — the widest pinned `ε*`-band in the tree.**
For `b ∣ n` with `b ≤ 4` (so the master collapse covers every band below the boundary),
the boundary-row dimension `k = n − 2b + 2`, and every `ε* ∈ [(b−1)/|F|, n/|F|)`:

  `mcaDeltaStar(RS[F, μ_n, k], ε*) = (b−1)/n` —

good below by the staircase collapse at bands `1, …, b−1` (`ε_mca ≤ (b−1)/q ≤ ε*`),
bad at the edge by the coset-clique certificate (`ε_mca ≥ n/q > ε*`).  At `b = 3`
the pinned band `[2/q, n/q)` spans `n − 2` granularity steps — the staircase jumps
from `2/q` directly to `≥ n/q` at the boundary radius, with no intermediate steps. -/
theorem mcaDeltaStar_eq_boundary [Nonempty (Fin n)] (hord : orderOf ζ = n)
    (hb2 : 2 ≤ b) (hb4 : b ≤ 4) (hbn : b ∣ n) (hbn2 : 2 * b < n)
    (hk : k = n - 2 * b + 2) {εstar : ℝ≥0∞}
    (hlo : ((b - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      (evalCode (smoothDom ζ n) k : Set (Fin n → F)) εstar
      = ((b : ℝ≥0) - 1) / (n : ℝ≥0) := by
  have hinj : Function.Injective (smoothDom ζ n) := smoothDom_injective ζ hord
  have hk_lo : n - 2 * b + 2 ≤ k := le_of_eq hk.symm
  have hk_hi : k ≤ n - b := by omega
  have hnpos : 0 < n := by omega
  refine le_antisymm
    (mcaDeltaStar_le_of_undersized_boundary ζ hord hb2 hbn hk_lo hk_hi hbn2 hhi) ?_
  by_contra h
  push_neg at h
  obtain ⟨c', hc1, hc2⟩ := exists_between h
  have hgood : epsMCA (F := F) (A := F)
      (evalCode (smoothDom ζ n) k : Set (Fin n → F)) c' ≤ εstar := by
    refine le_trans (MCAStaircaseMaster.epsMCA_le_div_card_of_dist _ (b - 1)
      (by omega)
      (ProximityGap.StripEdgeDeltaStar.evalCode_noWeightLE (smoothDom ζ n) hinj
        (by omega : 3 * (b - 1 - 1) + k ≤ n) (by omega))
      (by rw [Fintype.card_fin]; omega) ?_) ?_
    · -- c'·n < b − 1 from c' < (b−1)/n
      rw [Fintype.card_fin]
      have hb1cast : ((b : ℝ≥0) - 1) = ((b - 1 : ℕ) : ℝ≥0) := by
        rw [← NNReal.coe_inj]
        push_cast [Nat.cast_sub (by omega : 1 ≤ b),
          NNReal.coe_sub (by exact_mod_cast (by omega : 1 ≤ b) : (1 : ℝ≥0) ≤ (b : ℝ≥0))]
        ring
      calc c' * (n : ℝ≥0) < (((b : ℝ≥0) - 1) / (n : ℝ≥0)) * n := by
            have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
            exact mul_lt_mul_of_pos_right hc2 hn0
        _ = ((b - 1 : ℕ) : ℝ≥0) := by
            rw [hb1cast]
            field_simp
    · -- (b−1)/q ≤ ε*
      exact_mod_cast hlo
  have hcle : c' ≤ 1 := by
    refine le_of_lt (lt_of_lt_of_le hc2 ?_)
    rw [div_le_one (by exact_mod_cast hnpos : (0 : ℝ≥0) < (n : ℝ≥0))]
    calc (b : ℝ≥0) - 1 ≤ (b : ℝ≥0) := tsub_le_self
      _ ≤ (n : ℝ≥0) := by exact_mod_cast (by omega : b ≤ n)
  have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F) (A := F)
    (evalCode (smoothDom ζ n) k : Set (Fin n → F)) εstar hcle hgood
  exact absurd hle (not_le.mpr hc1)

end Boundary

end ProximityGap.CosetCliqueBoundary

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.CosetCliqueBoundary.clique_telescope
#print axioms ProximityGap.CosetCliqueBoundary.clique_mcaEvent
#print axioms ProximityGap.CosetCliqueBoundary.clique_eps_ge
#print axioms ProximityGap.CosetCliqueBoundary.mcaDeltaStar_le_of_undersized_boundary
#print axioms ProximityGap.CosetCliqueBoundary.mcaDeltaStar_eq_boundary
