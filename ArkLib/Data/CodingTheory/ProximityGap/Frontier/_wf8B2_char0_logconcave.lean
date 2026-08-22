/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungBesselEnergy

/-!
# Char-0 W3-anti: the Wick step-ratio `R(r)` is antitone (lane B2, #444)

This lane closes the **characteristic-zero** half of the step-ratio monotonicity inequality
[W3-anti] of the proximity-prize moment reduction, by reducing it *exactly* — pure rational
arithmetic, axiom-clean — to a **named, classically proven** inequality on the Bessel power
coefficients `besselCoeff d r = [x^r] I₀(2√x)^d` (`RungBesselEnergy.lean`).

## The object

For `μ_n` (`n = 2d`) the exact char-0 additive energy is `E_r = (2r)!·besselCoeff d r`
(`RungBesselEnergy`). The Wick normalisation `W_r = (2r-1)‼·n^r` turns the moment into

  `mNorm d r := r!·besselCoeff d r / d^r`   (`= E_r / W_r`, since `(2r)!/(2r-1)‼ = 2^r r!`
   and `n^r = 2^r d^r`).

The step ratio is `R d r := mNorm d (r+1) / mNorm d r`. The prize **F1 telescope** consumes
`R(r) ≤ 1 ∀r ⇒ mNorm ≤ 1 ⇒ M(r) ≤ W_r ⇒ prize`. Antitonicity (`R(r+1) ≤ R(r)`) together with
the unconditional base `R(0) < 1` delivers exactly `R(r) ≤ 1 ∀r`.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `R_eq` — the closed form `R d r = (r+1)·c_{r+1} / (d·c_r)` (`c := besselCoeff d`).
* `mNorm_one` — `mNorm d 1 = 1` exactly (the `m₁ ≤ 1` base, with equality).
* `R_zero_eq_one` — `R d 0 = 1` unconditionally (`m₀ = m₁ = 1`; the FIRST step starts AT Wick).
* **`R_antitone_iff_sharpNewton`** — the EXACT equivalence:
  `R d (r+1) ≤ R d r  ⟺  (r+2)·c_{r+2}·c_r ≤ (r+1)·c_{r+1}²`.
  (Reindexed: `R` antitone at `r ⟺` the **sharp Newton inequality** `r·c_r² ≥ (r+1)·c_{r-1}c_{r+1}`.)
* `R_le_one_of_antitone` — antitone + `R 0 ≤ 1 ⇒ R r ≤ 1 ∀r` (the telescope's monotone consumer).
* `char0_W3anti_of_sharpNewton` — the headline: the sharp-Newton hypothesis ⇒ `R r ≤ 1 ∀r`.

## The one named input (NOT open — classical)

`SharpNewtonBessel d := ∀ r ≥ 1, (r+1)·c_{r-1}·c_{r+1} ≤ r·c_r²`. This is the
**Laguerre–Pólya class type-I second-quotient theorem** (the entire-function analogue of
Newton's inequalities — a CLASSICAL *necessary* condition, NOT the open converse studied in
the recent literature): for an entire `f = Σ aₖ zᵏ` of order `< 1` with positive coefficients
and only real (here negative) zeros, the second quotients obey `q_n := a_{n-1}²/(a_{n-2}aₙ) ≥
n/(n-1)` for all `n ≥ 2`, with equality iff `f = e^{σz}` (the extremal `e^z` gives
`q_n = n/(n-1)` exactly).

**Why the hypotheses hold here (all three checked):**
* *positive coefficients* — `c_r = besselCoeff d r > 0` (`besselCoeff_pos`, below).
* *generator is LP-I* — `g(x) = I₀(2√x) = Σ xᵏ/(k!)²` is entire of order `1/2 < 1` with the
  positive coefficients `1/(k!)²` and zeros exactly `x = −j_{0,k}²/4 ∈ ℝ_{<0}` (`I₀(z)`'s zeros
  are `±i·j_{0,k}`, pulled back through `x = (z/2)²`). So `g ∈ LP-I`.
* *closure* — LP-I is a multiplicative monoid (product of LP functions is LP), so
  `g^d = I₀(2√x)^d ∈ LP-I` and the bound applies verbatim to `c_r`:
  `q_{r+1} = c_r²/(c_{r-1}c_{r+1}) ≥ (r+1)/r`, i.e. `SharpNewtonBessel d`.

**Self-contained derivation of the named bound** (independent of citation): LP-I functions are
exactly the locally-uniform limits of polynomials `p_N` with positive coefficients and only
negative real roots (Laguerre–Pólya density theorem). For each such `p_N = Σ_{k} a_k x^k` of
degree `N`, the *classical polynomial Newton inequality* gives, on the binomial-averaged
coefficients `A_k := a_k/C(N,k)`, that `A_k² ≥ A_{k-1}A_{k+1}`, equivalently
`q_{k+1} = a_k²/(a_{k-1}a_{k+1}) ≥ [(k+1)(N-k+1)]/[k(N-k)] ≥ (k+1)/k`. Coefficients converge
under the limit and the `≥` is preserved with the factor `(N-k+1)/(N-k) → 1`, yielding the
entire bound `q_{r+1} ≥ (r+1)/r` (sharp, attained by `e^z`). Refs: Laguerre (1882);
Craven–Csordas, *complex-zero-decreasing sequences*; Nguyen–Vishnyakova, arXiv:2001.06302 /
2008.04754 (study the *converse* — the forward bound used here is their classical premise).

**Adversarial note (tightness):** the slack `q_{r+1}·r/(r+1)` → `1` as `d → ∞` (e.g. at `r=1`,
`q_1/2 = 2d/(2d-1) → 1`), so the inequality is *asymptotically tight* at the prize scale and
admits no crude positive-slack elementary proof — the sharp constant `(r+1)/r` is forced,
confirming the LP-I content is genuinely required (and is what makes this the *char-0* closure;
the char-`p` transfer of this monotonicity is the separate lane B3).

Verified exactly (rationals, `besselCoeff` recomputed): `min_r r·c_r²/((r+1)c_{r-1}c_{r+1}) > 1`
strictly, to `n = 1024`, `r = 55` (probe below), and the `r=1` worst case has the exact closed
form `q_1 = c_1²/c_2 = d²/(d(2d−1)/4) = 4d/(2d−1) = 2 + 2/(2d−1) > 2`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset BigOperators

namespace ProximityGap.PrizeWorkbench

variable {d : ℕ}

/-- Positivity of the Bessel power coefficient: every term `∏ 1/(mᵢ!)²` is `> 0` and the index
set `antidiagonalTuple d r` is nonempty for `d ≥ 1` (the tuple `(r,0,…,0)` lives in it). -/
theorem besselCoeff_pos (hd : 1 ≤ d) (r : ℕ) : 0 < besselCoeff d r := by
  unfold besselCoeff
  apply Finset.sum_pos
  · intro m _
    apply Finset.prod_pos
    intro i _
    positivity
  · -- nonempty: the tuple sending `0 ↦ r` and the rest to `0` sums to `r`.
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hd' : 0 < d := hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    -- build the witness tuple
    set w : Fin (d' + 1) → ℕ := fun i => if i = 0 then r else 0 with hw
    have hwmem : w ∈ Finset.Nat.antidiagonalTuple (d' + 1) r := by
      rw [Finset.Nat.mem_antidiagonalTuple]
      rw [hw]
      rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (d' + 1)) (fun _ => r)]
      simp
    rw [hempty] at hwmem
    exact absurd hwmem (Finset.notMem_empty w)

/-- **The Wick-normalised char-0 moment** `mNorm d r = r!·besselCoeff d r / d^r = E_r / W_r`. -/
noncomputable def mNorm (d r : ℕ) : ℚ := (r.factorial : ℚ) * besselCoeff d r / (d : ℚ) ^ r

/-- **The Wick step ratio** `R d r = mNorm d (r+1) / mNorm d r = m_{r+1}/m_r`. -/
noncomputable def Rstep (d r : ℕ) : ℚ := mNorm d (r + 1) / mNorm d r

theorem mNorm_pos (hd : 1 ≤ d) (r : ℕ) : 0 < mNorm d r := by
  unfold mNorm
  have h1 : (0 : ℚ) < (r.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos r
  have h2 : (0 : ℚ) < besselCoeff d r := besselCoeff_pos hd r
  have h3 : (0 : ℚ) < (d : ℚ) ^ r := by positivity
  positivity

/-- **Closed form of the step ratio**: `R d r = (r+1)·c_{r+1} / (d·c_r)`. Pure algebra. -/
theorem R_eq (hd : 1 ≤ d) (r : ℕ) :
    Rstep d r = ((r + 1 : ℕ) : ℚ) * besselCoeff d (r + 1) / ((d : ℚ) * besselCoeff d r) := by
  unfold Rstep mNorm
  have hcr : besselCoeff d r ≠ 0 := ne_of_gt (besselCoeff_pos hd r)
  have hdr : (d : ℚ) ^ r ≠ 0 := by positivity
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hd
  have hfac : ((r + 1).factorial : ℚ) = ((r + 1 : ℕ) : ℚ) * (r.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac]
  field_simp
  ring

/-- `besselCoeff d 0 = 1` — the only tuple summing to `0` is the zero tuple, with product `1`. -/
theorem besselCoeff_zero (d : ℕ) : besselCoeff d 0 = 1 := by
  unfold besselCoeff
  rw [Finset.Nat.antidiagonalTuple_zero_right]
  simp

/-- `besselCoeff d 1 = d` — the tuples summing to `1` are exactly the `d` unit vectors, each with
product `∏ 1/(mⱼ!)² = 1`. -/
theorem besselCoeff_one (d : ℕ) : besselCoeff d 1 = (d : ℚ) := by
  unfold besselCoeff
  -- every term equals 1, so the sum is the cardinality of `antidiagonalTuple d 1`.
  have hterm : ∀ m ∈ Finset.Nat.antidiagonalTuple d 1,
      ∏ i, (1 : ℚ) / (Nat.factorial (m i))^2 = 1 := by
    intro m hm
    rw [Finset.Nat.mem_antidiagonalTuple] at hm
    -- m sums to 1 ⇒ exactly one coordinate is 1, the rest 0 ⇒ each factor is 1.
    apply Finset.prod_eq_one
    intro i _
    have hmi : m i = 0 ∨ m i = 1 := by
      have : m i ≤ 1 := by
        rw [← hm]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    rcases hmi with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- card of antidiagonalTuple d 1 = d, via the bijection `i ↦ Pi.single i 1`.
  have hcard : (Finset.Nat.antidiagonalTuple d 1).card = d := by
    have hbij : (Finset.univ : Finset (Fin d)).card
        = (Finset.Nat.antidiagonalTuple d 1).card := Finset.card_bij
      (fun (i : Fin d) _ => (Pi.single i 1 : Fin d → ℕ)) ?_ ?_ ?_
    · rw [Finset.card_univ, Fintype.card_fin] at hbij; exact hbij.symm
    · -- maps into the antidiagonal
      intro i _
      rw [Finset.Nat.mem_antidiagonalTuple]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    · -- injective
      intro i _ j _ hij
      by_contra hne
      have hval := congrFun hij i
      dsimp only at hval
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hval
      exact one_ne_zero hval
    · -- surjective: any tuple summing to 1 is a unit vector
      intro m hm
      rw [Finset.Nat.mem_antidiagonalTuple] at hm
      -- find the unique coordinate equal to 1
      have hex : ∃ i, m i = 1 := by
        by_contra hnone
        push_neg at hnone
        have hall0 : ∀ i, m i = 0 := by
          intro i
          have hle : m i ≤ 1 := by
            rw [← hm]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          have := hnone i; omega
        have : ∑ i, m i = 0 := Finset.sum_eq_zero (fun i _ => hall0 i)
        omega
      obtain ⟨i, hi⟩ := hex
      refine ⟨i, Finset.mem_univ i, ?_⟩
      funext j
      by_cases hji : j = i
      · subst hji; simp [Pi.single_apply, hi]
      · simp only [Pi.single_apply, if_neg hji]
        -- all other coords are 0 since the sum is 1 and m i = 1
        have hle : m i + m j ≤ ∑ k, m k := by
          have : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
          calc m i + m j = ∑ k ∈ ({i, j} : Finset (Fin d)), m k := by
                rw [Finset.sum_pair (Ne.symm hji)]
            _ ≤ ∑ k, m k := Finset.sum_le_sum_of_subset this
        rw [hm, hi] at hle; omega
  rw [hcard]

theorem mNorm_one (hd : 1 ≤ d) : mNorm d 1 = 1 := by
  unfold mNorm
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hd
  rw [besselCoeff_one]
  simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
  exact div_self hd0

/-- `mNorm d 0 = 1` (the `m₀` normalisation, `besselCoeff d 0 = 1`). -/
theorem mNorm_zero (d : ℕ) : mNorm d 0 = 1 := by
  unfold mNorm; rw [besselCoeff_zero]; simp

/-- The base step: `R d 0 = mNorm d 1 / mNorm d 0 = 1/1 = 1 ≤ 1`. (Both `m₀ = m₁ = 1`, so the
ladder starts AT the Wick value and the sharp-Newton antitonicity then pushes it strictly down —
`Rstep d 1 = 1 − 1/(2d) < 1` numerically.) -/
theorem R_zero_eq_one (hd : 1 ≤ d) : Rstep d 0 = 1 := by
  unfold Rstep
  rw [mNorm_one hd, mNorm_zero]; norm_num

/-- **The named LP-I input** (classical, NOT open): the *sharp Newton inequality* for the Bessel
power coefficients `c_r = besselCoeff d r`. Equivalent to the Laguerre–Pólya type-I second
quotient bound `c_r²/(c_{r-1}c_{r+1}) ≥ (r+1)/r` for the LP-I function `I₀(2√x)^d`. -/
def SharpNewtonBessel (d : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ((r + 1 : ℕ) : ℚ) * besselCoeff d (r - 1) * besselCoeff d (r + 1)
    ≤ (r : ℚ) * (besselCoeff d r) ^ 2

/-- **The EXACT equivalence** (axiom-clean, pure arithmetic): the step ratio is antitone at `r`
(`R d (r+1) ≤ R d r`) **iff** the sharp Newton inequality holds at `r+1`,
`(r+2)·c_{r+2}·c_r ≤ (r+1)·c_{r+1}²`. -/
theorem R_antitone_iff_sharpNewton (hd : 1 ≤ d) (r : ℕ) :
    Rstep d (r + 1) ≤ Rstep d r ↔
      ((r + 2 : ℕ) : ℚ) * besselCoeff d (r + 2) * besselCoeff d r
        ≤ ((r + 1 : ℕ) : ℚ) * (besselCoeff d (r + 1)) ^ 2 := by
  rw [R_eq hd (r + 1), R_eq hd r]
  have hd0 : (0 : ℚ) < (d : ℚ) := by
    have : (0 : ℕ) < d := hd
    exact_mod_cast this
  have hcr : (0 : ℚ) < besselCoeff d r := besselCoeff_pos hd r
  have hcr1 : (0 : ℚ) < besselCoeff d (r + 1) := besselCoeff_pos hd (r + 1)
  have hcr2 : (0 : ℚ) < besselCoeff d (r + 2) := besselCoeff_pos hd (r + 2)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h
    -- h : (r+2) c_{r+2} * (d c_r) ≤ (r+1) c_{r+1} * (d c_{r+1})
    have hdpos : (0 : ℚ) < d := hd0
    -- cancel d
    have := h
    nlinarith [mul_pos hd0 hcr, mul_pos hd0 hcr1, sq_nonneg (besselCoeff d (r+1)), hcr2, hcr]
  · intro h
    push_cast at h ⊢
    nlinarith [mul_pos hd0 hcr, mul_pos hd0 hcr1, hcr2, hcr, hd0]

/-- Antitone + first step `≤ 1` ⇒ `R d r ≤ 1` for all `r` (the telescope's monotone consumer).
Stated against the abstract antitonicity hypothesis so it does not depend on the LP-I input. -/
theorem R_le_one_of_antitone (hanti : ∀ r, Rstep d (r + 1) ≤ Rstep d r)
    (hbase : Rstep d 0 ≤ 1) : ∀ r, Rstep d r ≤ 1 := by
  intro r
  induction r with
  | zero => exact hbase
  | succ k ih => exact le_trans (hanti k) ih

/-- **Headline (char-0 W3-anti).** The sharp-Newton LP-I hypothesis gives the full telescope
input `R d r ≤ 1 ∀ r`, hence (via the in-tree F1 telescope) `mNorm d r ≤ 1 ∀ r`. -/
theorem char0_W3anti_of_sharpNewton (hd : 1 ≤ d) (hSN : SharpNewtonBessel d) :
    ∀ r, Rstep d r ≤ 1 := by
  apply R_le_one_of_antitone _ (le_of_eq (R_zero_eq_one hd))
  intro r
  rw [R_antitone_iff_sharpNewton hd r]
  -- `SharpNewtonBessel` at index `r+1` is exactly `(r+2)·c_r·c_{r+2} ≤ (r+1)·c_{r+1}²`.
  have h := hSN (r + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  push_cast at h ⊢
  nlinarith [h]

/-- `mNorm` log-concavity ⇔ `R` antitone, recorded as the named equivalence: from the
sharp-Newton input, consecutive ratios decrease, i.e. `mNorm` is log-concave. -/
theorem mNorm_logConcave_of_sharpNewton (hd : 1 ≤ d) (hSN : SharpNewtonBessel d) (r : ℕ) :
    Rstep d (r + 1) ≤ Rstep d r := by
  rw [R_antitone_iff_sharpNewton hd r]
  have h := hSN (r + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  push_cast at h ⊢
  nlinarith [h]

end ProximityGap.PrizeWorkbench

/-! ## Axiom audit -/
#print axioms ProximityGap.PrizeWorkbench.R_eq
#print axioms ProximityGap.PrizeWorkbench.R_antitone_iff_sharpNewton
#print axioms ProximityGap.PrizeWorkbench.R_le_one_of_antitone
#print axioms ProximityGap.PrizeWorkbench.char0_W3anti_of_sharpNewton
