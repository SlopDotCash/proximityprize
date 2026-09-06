/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R395: Selberg-majorant trim at depth 2 — the HBK-conditional fourth-moment ceiling

(#466 Gauss-phase PAPR arc, session 2026-07-09; route `selberg-majorant-trim`.
Predecessors in this lane: `_R339` Mellin identity, `_R340` autocorrelation,
`_R341CAZACCosetEquivalence` + `_R341MellinParseval` (the exact dictionary and the
depth-1 average), `_R342MellinLevelSet` (the depth-1 Chebyshev trim),
`_R343MellinFourthMoment` (the frequency-side exact fourth moment). This brick is the
COSET side of depth 2: trimming the exceptional frequency set of the Mellin PAPR sum
through the additive energy of the subgroup of `m`-th powers, conditional on the
published Heath-Brown–Konyagin subgroup-energy bound.)

## Dictionary

For `p` prime, `m ∣ p−1`, `n = (p−1)/m`, `H = {xᵐ : x ∈ F_p^*}` (so `|H| = n`), and the
normalized Mellin PAPR sum `M(t) = ∑_{j=1}^{m−1} u_j t^{−j}` (`u_j = g(χ^j)/√p`,
`t ∈ μ_m`), the r341 dictionary `M(χ(a)) = (m·S_a + 1)/√p` collapses the depth-2 moment
to coset statistics:

  `p(p−1)·∑_{t∈μ_m} |M(t)|⁴ = m·(m⁴·E(H) + 4m³·T(H) + 2m²·D(H) + 4m²·n + 1 − p³)`  (†)

with `quadEnergy` `E(H) = #{(x₁,x₂,x₃,x₄) ∈ H⁴ : x₁+x₂ = x₃+x₄}`,
`tripleCount` `T(H) = #{(x,y,z) ∈ H³ : x+y = z}`, `dTerm` `D(H) = n·[−1 ∈ H]`.
Probe: `scripts/probes/probe_r395_energy_certificates.py` verifies (†) to ≤ 1e-15 and
the exact `E,T,D` values at `(p,m) = (13,4), (29,7), (41,10), (61,12)`.

## PROVEN here (machine-checked, axiom-clean, unconditional)

* `tripleCount_le_sq`, `quadEnergy_le_cube`, `sq_le_quadEnergy`, `dTerm_le_card` —
  the counting bounds `T ≤ n²`, `n² ≤ E ≤ n³`, `D ≤ n`.
* `card_mul_pow_le_fourthMoment`, `exceptional_count_le`, `norm_le_fourthMoment_rpow`
  — the depth-2 Chebyshev (power-4 majorant) trim for ANY finite family:
  `#{i : λ ≤ ‖v i‖}·λ⁴ ≤ ∑‖v‖⁴` and `‖v i‖ ≤ (∑‖v‖⁴)^{1/4}`.
* `fourthMoment_le_of_energy_le` — the exact-arithmetic core: IF the (†)-shaped
  identity holds and `E ≤ C₁·n^{5/2}`, `T ≤ n²`, `D ≤ n`, THEN
  `∑_t |M(t)|⁴ ≤ (C₁+11)·m^{5/2}·√p`. The constant `C₁+11` uses only the trivial
  `T ≤ n²` (no Cauchy–Schwarz); for `C₁ ≥ 1` it is at least as sharp as the session
  write-up's `C₁+4√C₁+7`.
* `window_of_cubeRoot_le` — `m ≥ p^{1/3}` forces `n ≤ p^{2/3}` (the HBK window).
* Kernel-`decide` certificates (no `native_decide`) at `(p,m) = (13,4), (29,7),
  (41,10), (61,12)`: the power coset `H`, `E = 15/36/36/45`, `T = 0`, `D = 0/4/4/0`,
  and the parity-dichotomy instances `−1 ∈ H ⟺ n even`. All match the probe.

## CONDITIONAL consumers (hypotheses NAMED, nothing discharged)

* `mellin_fourthMoment_le_of_HBK`, `mellin_exceptional_count_of_HBK`,
  `mellin_max_of_HBK`: given (a) `HBKSubgroupEnergy C₁` and (b) the (†) identity as an
  explicit hypothesis `hid`, conclude for `m ≥ p^{1/3}`:
  `∑_t |M(t)|⁴ ≤ (C₁+11)·m^{5/2}·√p`;
  `#{t : |M(t)| ≥ λ} ≤ (C₁+11)·m^{5/2}·√p/λ⁴` (beats the r342 Parseval trim
  `m(m−1)/λ²` precisely when `λ ≳ (mp)^{1/4}`);
  `max_t |M(t)| ≤ (C₁+11)^{1/4}·m^{5/8}·p^{1/8}` — strictly inside `min(m−1, √p)`
  exactly in the window `p^{1/3} ≪ m ≪ p^{3/5}`.

## NAMED OPEN (do not discharge)

* `HBKSubgroupEnergy C₁` — Heath-Brown–Konyagin (Q. J. Math. 51 (2000), 221–235,
  Stepanov method): `E(H) ≤ C₁·n^{5/2}` for multiplicative subgroups `H ≤ F_p^*` with
  `n ≤ p^{2/3}`. PUBLISHED but not formalized (Shkredov's `n^{32/13}`-type refinements
  would only sharpen it). Consumed only by the `*_of_HBK` theorems.
* The (†) identity enters the consumers as the hypothesis `hid`: its frequency-side
  form is proved in `_R343MellinFourthMoment.mellin_fourth_moment`; the coset-side
  weld through the r341 dictionary is a separate brick. Probe-verified exactly here at
  four `(p,m)` pairs.
* The prize wall is NOT moved: for `m ≤ p^{1/3}` the HBK window is empty, and in the
  middle window the per-`(p,m)` bound `√(m log p)` (`MellinCAZACBound` /
  `SubgroupCosetSqrtCancellation` in `_R341CAZACCosetEquivalence`) remains open in
  both directions. Within the Cauchy–Schwarz chaining scheme `E_k ≤ n²E_{k−1}` depth 2
  is optimal below `m ≈ p^{3/5}`; direct higher-energy Stepanov bounds are NOT
  excluded by this file.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim

/-! ## The coset-side statistics of (†) -/

/-- Ordered additive (2+2)-energy of a finite subset of `ZMod p`:
`E(H) = #{(x₁,x₂,x₃,x₄) ∈ H⁴ : x₁+x₂ = x₃+x₄}`. -/
def quadEnergy {p : ℕ} (H : Finset (ZMod p)) : ℕ :=
  (((H ×ˢ H) ×ˢ H ×ˢ H).filter fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2).card

/-- Ordered triple count `T(H) = #{(x,y,z) ∈ H³ : x+y = z}`. -/
def tripleCount {p : ℕ} (H : Finset (ZMod p)) : ℕ :=
  ((H ×ˢ H ×ˢ H).filter fun q => q.1 + q.2.1 = q.2.2).card

/-- The parity term `D(H) = |H|·[−1 ∈ H]` of (†). -/
def dTerm {p : ℕ} (H : Finset (ZMod p)) : ℕ :=
  if (-1 : ZMod p) ∈ H then H.card else 0

theorem dTerm_le_card {p : ℕ} (H : Finset (ZMod p)) : dTerm H ≤ H.card := by
  unfold dTerm
  split <;> simp

/-- Trivial bound `T(H) ≤ |H|²`: the target `z = x + y` is determined by `(x,y)`. -/
theorem tripleCount_le_sq {p : ℕ} (H : Finset (ZMod p)) :
    tripleCount H ≤ H.card ^ 2 := by
  have h : ((H ×ˢ H ×ˢ H).filter fun q => q.1 + q.2.1 = q.2.2).card ≤ (H ×ˢ H).card := by
    apply Finset.card_le_card_of_injOn (fun q => (q.1, q.2.1))
    · rintro ⟨a, b, c⟩ hq
      have hq' := Finset.mem_coe.mp hq
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hq').1
      have hbc := Finset.mem_product.mp hmem.2
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hmem.1, hbc.1⟩)
    · rintro ⟨a, b, c⟩ hq ⟨a', b', c'⟩ hq' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hf : a + b = c := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have hf' : a + b = c' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
      have hcc : c = c' := hf.symm.trans hf'
      rw [hcc]
  calc tripleCount H ≤ (H ×ˢ H).card := h
    _ = H.card ^ 2 := by rw [Finset.card_product, sq]

/-- Trivial bound `E(H) ≤ |H|³`: `x₄ = x₁ + x₂ − x₃` is determined by `(x₁,x₂,x₃)`. -/
theorem quadEnergy_le_cube {p : ℕ} (H : Finset (ZMod p)) :
    quadEnergy H ≤ H.card ^ 3 := by
  have h : (((H ×ˢ H) ×ˢ H ×ˢ H).filter fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2).card
      ≤ ((H ×ˢ H) ×ˢ H).card := by
    apply Finset.card_le_card_of_injOn (fun q => (q.1, q.2.1))
    · rintro ⟨⟨a, b⟩, c, d⟩ hq
      have hq' := Finset.mem_coe.mp hq
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hq').1
      have hcd := Finset.mem_product.mp hmem.2
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hmem.1, hcd.1⟩)
    · rintro ⟨⟨a, b⟩, c, d⟩ hq ⟨⟨a', b'⟩, c', d'⟩ hq' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      have hf : a + b = c + d := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have hf' : a + b = c + d' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
      have hdd : d = d' := add_left_cancel (hf.symm.trans hf')
      rw [hdd]
  calc quadEnergy H ≤ ((H ×ˢ H) ×ˢ H).card := h
    _ = H.card ^ 3 := by rw [Finset.card_product, Finset.card_product]; ring

/-- Diagonal lower bound `|H|² ≤ E(H)` (the Wick floor of (†)'s main term). -/
theorem sq_le_quadEnergy {p : ℕ} (H : Finset (ZMod p)) :
    H.card ^ 2 ≤ quadEnergy H := by
  have h : (H ×ˢ H).card
      ≤ (((H ×ˢ H) ×ˢ H ×ˢ H).filter fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2).card := by
    apply Finset.card_le_card_of_injOn (fun q => (q, q))
    · rintro ⟨a, b⟩ hq
      have hq' := Finset.mem_coe.mp hq
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq', hq'⟩, rfl⟩)
    · rintro q hq q' hq' heq
      exact congrArg Prod.fst heq
  calc H.card ^ 2 = (H ×ˢ H).card := by rw [Finset.card_product, sq]
    _ ≤ _ := h

/-! ## The named open hypothesis -/

/-- **NAMED OPEN (do not discharge): the Heath-Brown–Konyagin subgroup-energy bound.**
For every prime `p` and every multiplicative subgroup `H` of `F_p^*` (encoded as a
finite, multiplicatively closed set of nonzero elements containing `1`) with
`|H| ≤ p^{2/3}`, the additive energy satisfies `E(H) ≤ C₁·|H|^{5/2}`.

Published: Heath-Brown–Konyagin, Q. J. Math. 51 (2000) 221–235 (Stepanov method);
not formalized in Lean. Consumed ONLY by the `*_of_HBK` theorems below. -/
def HBKSubgroupEnergy (C₁ : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ H : Finset (ZMod p),
    (1 : ZMod p) ∈ H → (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) → (0 : ZMod p) ∉ H →
    (H.card : ℝ) ≤ (p : ℝ) ^ ((2 : ℝ) / 3) →
    (quadEnergy H : ℝ) ≤ C₁ * (H.card : ℝ) ^ ((5 : ℝ) / 2)

/-! ## The depth-2 Chebyshev (majorant) trim — unconditional, any finite family -/

/-- Power-4 Chebyshev: `#{i ∈ T : λ ≤ ‖v i‖}·λ⁴ ≤ ∑_{i∈T} ‖v i‖⁴`. -/
theorem card_mul_pow_le_fourthMoment {ι : Type*} (Tf : Finset ι) (v : ι → ℂ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ((Tf.filter fun i => lam ≤ ‖v i‖).card : ℝ) * lam ^ 4 ≤ ∑ i ∈ Tf, ‖v i‖ ^ 4 := by
  classical
  calc ((Tf.filter fun i => lam ≤ ‖v i‖).card : ℝ) * lam ^ 4
      = ∑ _i ∈ Tf.filter fun i => lam ≤ ‖v i‖, lam ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Tf.filter fun i => lam ≤ ‖v i‖, ‖v i‖ ^ 4 := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact pow_le_pow_left₀ hlam (Finset.mem_filter.mp hi).2 4
    _ ≤ ∑ i ∈ Tf, ‖v i‖ ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by positivity

/-- Exceptional-set count from a fourth-moment bound. -/
theorem exceptional_count_le {ι : Type*} (Tf : Finset ι) (v : ι → ℂ)
    {S₄ lam : ℝ} (hlam : 0 < lam) (hS : ∑ i ∈ Tf, ‖v i‖ ^ 4 ≤ S₄) :
    ((Tf.filter fun i => lam ≤ ‖v i‖).card : ℝ) ≤ S₄ / lam ^ 4 := by
  rw [le_div_iff₀ (by positivity)]
  exact le_trans (card_mul_pow_le_fourthMoment Tf v hlam.le) hS

/-- Sup bound from a fourth-moment bound: `‖v i‖ ≤ S₄^{1/4}`. -/
theorem norm_le_fourthMoment_rpow {ι : Type*} {Tf : Finset ι} {v : ι → ℂ} {S₄ : ℝ}
    (hS : ∑ i ∈ Tf, ‖v i‖ ^ 4 ≤ S₄) {i : ι} (hi : i ∈ Tf) :
    ‖v i‖ ≤ S₄ ^ ((1 : ℝ) / 4) := by
  have h4 : ‖v i‖ ^ 4 ≤ S₄ :=
    le_trans (Finset.single_le_sum (f := fun j => ‖v j‖ ^ 4)
      (fun j _ => by positivity) hi) hS
  have hnn : (0 : ℝ) ≤ ‖v i‖ := norm_nonneg _
  have key : ‖v i‖ = (‖v i‖ ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast (‖v i‖) 4, ← Real.rpow_mul hnn]
    norm_num
  rw [key]
  exact Real.rpow_le_rpow (by positivity) h4 (by norm_num)

/-! ## Window arithmetic -/

/-- `m ≥ p^{1/3}` forces `n ≤ p^{2/3}` when `m·n = p − 1`: the HBK window in the
`m`-variable. -/
theorem window_of_cubeRoot_le {p m n : ℝ} (hp : 0 < p) (hn : 0 ≤ n)
    (hmn : m * n = p - 1) (hwin : p ^ ((1 : ℝ) / 3) ≤ m) :
    n ≤ p ^ ((2 : ℝ) / 3) := by
  have hp13 : (0 : ℝ) < p ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hp _
  have h1 : n * p ^ ((1 : ℝ) / 3) ≤ p ^ ((2 : ℝ) / 3) * p ^ ((1 : ℝ) / 3) := by
    calc n * p ^ ((1 : ℝ) / 3) ≤ n * m := mul_le_mul_of_nonneg_left hwin hn
      _ = p - 1 := by rw [mul_comm, hmn]
      _ ≤ p := by linarith
      _ = p ^ ((2 : ℝ) / 3) * p ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_add hp]
          norm_num
  exact le_of_mul_le_mul_right h1 hp13

/-! ## The exact-arithmetic core -/

/-- **The depth-2 majorant core.** If the (†)-shaped identity holds and
`E ≤ C₁·n^{5/2}`, `T ≤ n²`, `D ≤ n`, `m·n = p−1`, then
`S₄ ≤ (C₁+11)·m^{5/2}·√p`. Pure real arithmetic; the constant `C₁+11` needs only the
trivial `T ≤ n²` (for `C₁ ≥ 1` it is ≤ the write-up's `C₁+4√C₁+7`). -/
theorem fourthMoment_le_of_energy_le
    {p m n E T D S₄ C₁ : ℝ}
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hn : 1 ≤ n) (hC0 : 0 ≤ C₁)
    (hmn : m * n = p - 1)
    (hid : p * (p - 1) * S₄
      = m * (m ^ 4 * E + 4 * m ^ 3 * T + 2 * m ^ 2 * D + 4 * m ^ 2 * n + 1 - p ^ 3))
    (hE : E ≤ C₁ * n ^ ((5 : ℝ) / 2))
    (hT : T ≤ n * n)
    (hD : D ≤ n) :
    S₄ ≤ (C₁ + 11) * m ^ ((5 : ℝ) / 2) * Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  -- rpow bookkeeping
  have hm5 : m ^ (5 : ℕ) = m ^ ((5 : ℝ) / 2) * m ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_natCast m 5]
    norm_num
  have hmn52 : m ^ ((5 : ℝ) / 2) * n ^ ((5 : ℝ) / 2) = (p - 1) ^ ((5 : ℝ) / 2) := by
    rw [← Real.mul_rpow hm0.le hn0.le, hmn]
  have hp52 : (p - 1) ^ ((5 : ℝ) / 2) = (p - 1) ^ ((3 : ℝ) / 2) * (p - 1) := by
    calc (p - 1) ^ ((5 : ℝ) / 2) = (p - 1) ^ ((3 : ℝ) / 2 + 1) := by norm_num
      _ = (p - 1) ^ ((3 : ℝ) / 2) * (p - 1) ^ (1 : ℝ) := Real.rpow_add hp1 _ _
      _ = (p - 1) ^ ((3 : ℝ) / 2) * (p - 1) := by rw [Real.rpow_one]
  have hp32le : (p - 1) ^ ((3 : ℝ) / 2) ≤ p ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hp1.le (by linarith) (by norm_num)
  have hm2le : m ^ (2 : ℕ) ≤ m ^ ((5 : ℝ) / 2) := by
    calc m ^ (2 : ℕ) = m ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast m 2).symm
      _ ≤ m ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hmle : m ≤ m ^ ((5 : ℝ) / 2) := by
    calc m = m ^ (1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ m ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hp32pos : (0 : ℝ) < p ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hone_p32 : (1 : ℝ) ≤ p ^ ((3 : ℝ) / 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 2) := (Real.one_rpow _).symm
      _ ≤ p ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow zero_le_one (by linarith) (by norm_num)
  have hple32 : p - 1 ≤ p ^ ((3 : ℝ) / 2) := by
    calc p - 1 ≤ p := by linarith
      _ = p ^ (1 : ℝ) := (Real.rpow_one p).symm
      _ ≤ p ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  set B := m ^ ((5 : ℝ) / 2) * p ^ ((3 : ℝ) / 2) * (p - 1) with hB
  have hm52pos : (0 : ℝ) < m ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hm0 _
  -- the five term bounds
  have h1 : m * (m ^ 4 * E) ≤ C₁ * B := by
    have e1 : m * (m ^ 4 * E) = m ^ (5 : ℕ) * E := by ring
    have e2 : m ^ (5 : ℕ) * E ≤ m ^ (5 : ℕ) * (C₁ * n ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have e3 : m ^ (5 : ℕ) * (C₁ * n ^ ((5 : ℝ) / 2))
        = C₁ * (m ^ ((5 : ℝ) / 2) * ((p - 1) ^ ((3 : ℝ) / 2) * (p - 1))) := by
      calc m ^ (5 : ℕ) * (C₁ * n ^ ((5 : ℝ) / 2))
          = C₁ * (m ^ ((5 : ℝ) / 2) * (m ^ ((5 : ℝ) / 2) * n ^ ((5 : ℝ) / 2))) := by
            rw [hm5]; ring
        _ = C₁ * (m ^ ((5 : ℝ) / 2) * (p - 1) ^ ((5 : ℝ) / 2)) := by rw [hmn52]
        _ = C₁ * (m ^ ((5 : ℝ) / 2) * ((p - 1) ^ ((3 : ℝ) / 2) * (p - 1))) := by rw [hp52]
    have e4 : C₁ * (m ^ ((5 : ℝ) / 2) * ((p - 1) ^ ((3 : ℝ) / 2) * (p - 1)))
        ≤ C₁ * (m ^ ((5 : ℝ) / 2) * (p ^ ((3 : ℝ) / 2) * (p - 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      apply mul_le_mul_of_nonneg_left _ hm52pos.le
      exact mul_le_mul_of_nonneg_right hp32le hp1.le
    calc m * (m ^ 4 * E) = m ^ (5 : ℕ) * E := e1
      _ ≤ m ^ (5 : ℕ) * (C₁ * n ^ ((5 : ℝ) / 2)) := e2
      _ = C₁ * (m ^ ((5 : ℝ) / 2) * ((p - 1) ^ ((3 : ℝ) / 2) * (p - 1))) := e3
      _ ≤ C₁ * (m ^ ((5 : ℝ) / 2) * (p ^ ((3 : ℝ) / 2) * (p - 1))) := e4
      _ = C₁ * B := by rw [hB]; ring
  have h2 : m * (4 * m ^ 3 * T) ≤ 4 * B := by
    have e1 : m * (4 * m ^ 3 * T) = 4 * (m ^ (4 : ℕ) * T) := by ring
    have e2 : m ^ (4 : ℕ) * T ≤ m ^ (4 : ℕ) * (n * n) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have e3 : m ^ (4 : ℕ) * (n * n) = (p - 1) * ((p - 1) * m ^ (2 : ℕ)) := by
      calc m ^ (4 : ℕ) * (n * n) = (m * n) * ((m * n) * m ^ (2 : ℕ)) := by ring
        _ = (p - 1) * ((p - 1) * m ^ (2 : ℕ)) := by rw [hmn]
    have e4 : (p - 1) * ((p - 1) * m ^ (2 : ℕ))
        ≤ (p - 1) * (p ^ ((3 : ℝ) / 2) * m ^ ((5 : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hp1.le
      exact mul_le_mul hple32 hm2le (by positivity) hp32pos.le
    calc m * (4 * m ^ 3 * T) = 4 * (m ^ (4 : ℕ) * T) := e1
      _ ≤ 4 * ((p - 1) * (p ^ ((3 : ℝ) / 2) * m ^ ((5 : ℝ) / 2))) := by
          have := le_trans e2 (le_of_eq e3)
          have := le_trans this e4
          linarith
      _ = 4 * B := by rw [hB]; ring
  have hm3n : m ^ (3 : ℕ) * n = m ^ (2 : ℕ) * (p - 1) := by
    calc m ^ (3 : ℕ) * n = m ^ (2 : ℕ) * (m * n) := by ring
      _ = m ^ (2 : ℕ) * (p - 1) := by rw [hmn]
  have hm2B : m ^ (2 : ℕ) * (p - 1) ≤ B := by
    rw [hB]
    have e5 : m ^ (2 : ℕ) ≤ m ^ ((5 : ℝ) / 2) * p ^ ((3 : ℝ) / 2) := by
      calc m ^ (2 : ℕ) ≤ m ^ ((5 : ℝ) / 2) := hm2le
        _ = m ^ ((5 : ℝ) / 2) * 1 := (mul_one _).symm
        _ ≤ m ^ ((5 : ℝ) / 2) * p ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hone_p32 hm52pos.le
    exact mul_le_mul_of_nonneg_right e5 hp1.le
  have h3 : m * (2 * m ^ 2 * D) ≤ 2 * B := by
    have e1 : m * (2 * m ^ 2 * D) = 2 * (m ^ (3 : ℕ) * D) := by ring
    have e2 : m ^ (3 : ℕ) * D ≤ m ^ (3 : ℕ) * n :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    calc m * (2 * m ^ 2 * D) = 2 * (m ^ (3 : ℕ) * D) := e1
      _ ≤ 2 * B := by
          have := le_trans e2 (le_of_eq hm3n)
          have := le_trans this hm2B
          linarith
  have h4 : m * (4 * m ^ 2 * n) ≤ 4 * B := by
    have e1 : m * (4 * m ^ 2 * n) = 4 * (m ^ (3 : ℕ) * n) := by ring
    calc m * (4 * m ^ 2 * n) = 4 * (m ^ (3 : ℕ) * n) := e1
      _ ≤ 4 * B := by
          have := le_trans (le_of_eq hm3n) hm2B
          linarith
  have h5 : m * 1 ≤ B := by
    rw [mul_one, hB]
    calc m ≤ m ^ ((5 : ℝ) / 2) := hmle
      _ = m ^ ((5 : ℝ) / 2) * 1 * 1 := by ring
      _ ≤ m ^ ((5 : ℝ) / 2) * p ^ ((3 : ℝ) / 2) * (p - 1) := by
          apply mul_le_mul _ (by linarith) zero_le_one (by positivity)
          exact mul_le_mul_of_nonneg_left hone_p32 hm52pos.le
  -- assemble
  have hdrop : m * (m ^ 4 * E + 4 * m ^ 3 * T + 2 * m ^ 2 * D + 4 * m ^ 2 * n + 1 - p ^ 3)
      ≤ m * (m ^ 4 * E) + m * (4 * m ^ 3 * T) + m * (2 * m ^ 2 * D)
        + m * (4 * m ^ 2 * n) + m * 1 := by
    have hexp : m * (m ^ 4 * E + 4 * m ^ 3 * T + 2 * m ^ 2 * D + 4 * m ^ 2 * n + 1 - p ^ 3)
        = m * (m ^ 4 * E) + m * (4 * m ^ 3 * T) + m * (2 * m ^ 2 * D)
          + m * (4 * m ^ 2 * n) + m * 1 - m * p ^ 3 := by ring
    have hmp3 : 0 ≤ m * p ^ 3 := by positivity
    rw [hexp]
    linarith
  have hkey : p * (p - 1) * S₄ ≤ (C₁ + 11) * B := by
    rw [hid]
    calc m * (m ^ 4 * E + 4 * m ^ 3 * T + 2 * m ^ 2 * D + 4 * m ^ 2 * n + 1 - p ^ 3)
        ≤ m * (m ^ 4 * E) + m * (4 * m ^ 3 * T) + m * (2 * m ^ 2 * D)
          + m * (4 * m ^ 2 * n) + m * 1 := hdrop
      _ ≤ C₁ * B + 4 * B + 2 * B + 4 * B + B := by linarith
      _ = (C₁ + 11) * B := by ring
  have hfin : p * (p - 1) * S₄
      ≤ p * (p - 1) * ((C₁ + 11) * m ^ ((5 : ℝ) / 2) * Real.sqrt p) := by
    refine hkey.trans (le_of_eq ?_)
    rw [hB, Real.sqrt_eq_rpow]
    have h32 : p ^ ((3 : ℝ) / 2) = p * p ^ (1 / (2 : ℝ)) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one]
    rw [h32]
    ring
  exact le_of_mul_le_mul_left hfin (mul_pos hp0 hp1)

/-! ## The conditional consumers (HBK + the (†) identity as named hypotheses) -/

/-- **Conditional fourth-moment ceiling.** Given `HBKSubgroupEnergy C₁` and the (†)
identity for the family `v` over the frequency index `Tf` (hypothesis `hid`; its
frequency-side form is `_R343.mellin_fourth_moment`, the coset-side weld is a separate
brick), for `m ≥ p^{1/3}`: `∑_t ‖v t‖⁴ ≤ (C₁+11)·m^{5/2}·√p`. -/
theorem mellin_fourthMoment_le_of_HBK
    {C₁ : ℝ} (hC0 : 0 ≤ C₁) (hbk : HBKSubgroupEnergy C₁)
    {p m n : ℕ} (hp : p.Prime) (hmn : m * n = p - 1) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    {H : Finset (ZMod p)} (h1H : (1 : ZMod p) ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (h0H : (0 : ZMod p) ∉ H)
    (hcard : H.card = n)
    (hwin : (p : ℝ) ^ ((1 : ℝ) / 3) ≤ (m : ℝ))
    {ι : Type*} {Tf : Finset ι} {v : ι → ℂ}
    (hid : (p : ℝ) * ((p : ℝ) - 1) * (∑ i ∈ Tf, ‖v i‖ ^ 4)
      = (m : ℝ) * ((m : ℝ) ^ 4 * (quadEnergy H : ℝ)
          + 4 * (m : ℝ) ^ 3 * (tripleCount H : ℝ)
          + 2 * (m : ℝ) ^ 2 * (dTerm H : ℝ) + 4 * (m : ℝ) ^ 2 * (n : ℝ) + 1
          - (p : ℝ) ^ 3)) :
    (∑ i ∈ Tf, ‖v i‖ ^ 4) ≤ (C₁ + 11) * (m : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmnR : (m : ℝ) * (n : ℝ) = (p : ℝ) - 1 := by
    have h1 : ((m * n : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) := by rw [hmn]
    rw [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h1
    exact h1
  have hwin' : (n : ℝ) ≤ (p : ℝ) ^ ((2 : ℝ) / 3) :=
    window_of_cubeRoot_le (by linarith) (by positivity) hmnR hwin
  have hcard' : (H.card : ℝ) ≤ (p : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hcard]; exact hwin'
  have hER : (quadEnergy H : ℝ) ≤ C₁ * (n : ℝ) ^ ((5 : ℝ) / 2) := by
    have h := hbk p hp H h1H hmul h0H hcard'
    rwa [hcard] at h
  have hTR : (tripleCount H : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    have h := tripleCount_le_sq H
    rw [hcard] at h
    calc (tripleCount H : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      _ = (n : ℝ) * (n : ℝ) := by push_cast; ring
  have hDR : (dTerm H : ℝ) ≤ (n : ℝ) := by
    have h := dTerm_le_card H
    rw [hcard] at h
    exact_mod_cast h
  exact fourthMoment_le_of_energy_le hp2 hm1' hn1' hC0 hmnR hid hER hTR hDR

/-- **Conditional λ⁻⁴ trim.** Under the same hypotheses, the exceptional frequency set
has size `≤ (C₁+11)·m^{5/2}·√p/λ⁴` — beating the r342 Parseval trim `m(m−1)/λ²`
precisely when `λ ≳ (mp)^{1/4}`. -/
theorem mellin_exceptional_count_of_HBK
    {C₁ : ℝ} (hC0 : 0 ≤ C₁) (hbk : HBKSubgroupEnergy C₁)
    {p m n : ℕ} (hp : p.Prime) (hmn : m * n = p - 1) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    {H : Finset (ZMod p)} (h1H : (1 : ZMod p) ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (h0H : (0 : ZMod p) ∉ H)
    (hcard : H.card = n)
    (hwin : (p : ℝ) ^ ((1 : ℝ) / 3) ≤ (m : ℝ))
    {ι : Type*} {Tf : Finset ι} {v : ι → ℂ}
    (hid : (p : ℝ) * ((p : ℝ) - 1) * (∑ i ∈ Tf, ‖v i‖ ^ 4)
      = (m : ℝ) * ((m : ℝ) ^ 4 * (quadEnergy H : ℝ)
          + 4 * (m : ℝ) ^ 3 * (tripleCount H : ℝ)
          + 2 * (m : ℝ) ^ 2 * (dTerm H : ℝ) + 4 * (m : ℝ) ^ 2 * (n : ℝ) + 1
          - (p : ℝ) ^ 3))
    {lam : ℝ} (hlam : 0 < lam) :
    ((Tf.filter fun i => lam ≤ ‖v i‖).card : ℝ)
      ≤ (C₁ + 11) * (m : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt p / lam ^ 4 :=
  exceptional_count_le Tf v hlam
    (mellin_fourthMoment_le_of_HBK hC0 hbk hp hmn hm1 hn1 h1H hmul h0H hcard hwin hid)

/-- **Conditional max ceiling with clean exponents:**
`max_t ‖v t‖ ≤ (C₁+11)^{1/4}·m^{5/8}·p^{1/8}` — strictly below both Weil (`m−1`) and
trivial (`√p`) exactly in the window `p^{1/3} ≪ m ≪ p^{3/5}`. -/
theorem mellin_max_of_HBK
    {C₁ : ℝ} (hC0 : 0 ≤ C₁) (hbk : HBKSubgroupEnergy C₁)
    {p m n : ℕ} (hp : p.Prime) (hmn : m * n = p - 1) (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    {H : Finset (ZMod p)} (h1H : (1 : ZMod p) ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (h0H : (0 : ZMod p) ∉ H)
    (hcard : H.card = n)
    (hwin : (p : ℝ) ^ ((1 : ℝ) / 3) ≤ (m : ℝ))
    {ι : Type*} {Tf : Finset ι} {v : ι → ℂ}
    (hid : (p : ℝ) * ((p : ℝ) - 1) * (∑ i ∈ Tf, ‖v i‖ ^ 4)
      = (m : ℝ) * ((m : ℝ) ^ 4 * (quadEnergy H : ℝ)
          + 4 * (m : ℝ) ^ 3 * (tripleCount H : ℝ)
          + 2 * (m : ℝ) ^ 2 * (dTerm H : ℝ) + 4 * (m : ℝ) ^ 2 * (n : ℝ) + 1
          - (p : ℝ) ^ 3))
    {i : ι} (hi : i ∈ Tf) :
    ‖v i‖ ≤ (C₁ + 11) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((5 : ℝ) / 8) * (p : ℝ) ^ ((1 : ℝ) / 8) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hS := mellin_fourthMoment_le_of_HBK hC0 hbk hp hmn hm1 hn1 h1H hmul h0H hcard
    hwin hid
  have h := norm_le_fourthMoment_rpow hS hi
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsplit : ((C₁ + 11) * (m : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt p) ^ ((1 : ℝ) / 4)
      = (C₁ + 11) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((5 : ℝ) / 8) * (p : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _),
      Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    · congr 1
      rw [← Real.rpow_mul hm0, show (5 : ℝ) / 2 * ((1 : ℝ) / 4) = 5 / 8 by norm_num]
    · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hp0.le,
        show (1 : ℝ) / 2 * ((1 : ℝ) / 4) = 1 / 8 by norm_num]
  rw [hsplit] at h
  exact h

/-! ## Kernel-`decide` certificates (match `probe_r395_energy_certificates.py`)

`powerCoset p m` is `H = {xᵐ : x ∈ F_p^*}`. At the four probe pairs the exact
statistics of (†) are certified below; note the parity dichotomy `−1 ∈ H ⟺ n even`
in the instances `n = 3, 4, 4, 5`. -/

/-- The multiplicative subgroup of `m`-th powers `{xᵐ : x ∈ F_p^*} ⊆ ZMod p`. -/
def powerCoset (p : ℕ) [NeZero p] (m : ℕ) : Finset (ZMod p) :=
  (Finset.univ.erase (0 : ZMod p)).image (· ^ m)

-- (p, m) = (13, 4): n = 3 (odd), E = 15, T = 0, D = 0, −1 ∉ H
theorem powerCoset_13_4 : powerCoset 13 4 = {1, 3, 9} := by decide
theorem quadEnergy_13_4 : quadEnergy (powerCoset 13 4) = 15 := by decide
theorem tripleCount_13_4 : tripleCount (powerCoset 13 4) = 0 := by decide
theorem dTerm_13_4 : dTerm (powerCoset 13 4) = 0 := by decide
theorem negOne_notMem_13_4 : (-1 : ZMod 13) ∉ powerCoset 13 4 := by decide

-- (p, m) = (29, 7): n = 4 (even), E = 36, T = 0, D = 4, −1 ∈ H
theorem powerCoset_29_7 : powerCoset 29 7 = {1, 12, 17, 28} := by decide
theorem quadEnergy_29_7 : quadEnergy (powerCoset 29 7) = 36 := by decide
theorem tripleCount_29_7 : tripleCount (powerCoset 29 7) = 0 := by decide
theorem dTerm_29_7 : dTerm (powerCoset 29 7) = 4 := by decide
theorem negOne_mem_29_7 : (-1 : ZMod 29) ∈ powerCoset 29 7 := by decide

-- (p, m) = (41, 10): n = 4 (even), E = 36, T = 0, D = 4, −1 ∈ H
theorem powerCoset_41_10 : powerCoset 41 10 = {1, 9, 32, 40} := by decide
theorem quadEnergy_41_10 : quadEnergy (powerCoset 41 10) = 36 := by decide
theorem tripleCount_41_10 : tripleCount (powerCoset 41 10) = 0 := by decide
theorem dTerm_41_10 : dTerm (powerCoset 41 10) = 4 := by decide
theorem negOne_mem_41_10 : (-1 : ZMod 41) ∈ powerCoset 41 10 := by decide

-- (p, m) = (61, 12): n = 5 (odd), E = 45, T = 0, D = 0, −1 ∉ H
theorem powerCoset_61_12 : powerCoset 61 12 = {1, 9, 20, 34, 58} := by decide
theorem quadEnergy_61_12 : quadEnergy (powerCoset 61 12) = 45 := by decide
theorem tripleCount_61_12 : tripleCount (powerCoset 61 12) = 0 := by decide
theorem dTerm_61_12 : dTerm (powerCoset 61 12) = 0 := by decide
theorem negOne_notMem_61_12 : (-1 : ZMod 61) ∉ powerCoset 61 12 := by decide

end ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/

open ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim

#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.dTerm_le_card
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.tripleCount_le_sq
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.quadEnergy_le_cube
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.sq_le_quadEnergy
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.card_mul_pow_le_fourthMoment
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.exceptional_count_le
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.norm_le_fourthMoment_rpow
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.window_of_cubeRoot_le
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.fourthMoment_le_of_energy_le
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.mellin_fourthMoment_le_of_HBK
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.mellin_exceptional_count_of_HBK
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.mellin_max_of_HBK
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.powerCoset_13_4
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.quadEnergy_13_4
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.tripleCount_13_4
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.dTerm_13_4
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.negOne_notMem_13_4
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.powerCoset_29_7
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.quadEnergy_29_7
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.tripleCount_29_7
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.dTerm_29_7
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.negOne_mem_29_7
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.powerCoset_41_10
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.quadEnergy_41_10
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.tripleCount_41_10
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.dTerm_41_10
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.negOne_mem_41_10
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.powerCoset_61_12
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.quadEnergy_61_12
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.tripleCount_61_12
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.dTerm_61_12
#print axioms ArkLib.ProximityGap.R395MellinFourthMomentHBKTrim.negOne_notMem_61_12
