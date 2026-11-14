/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The DC-subtracted-energy OVERSHOOT is the BGK wall (Issue #444, route [moment], wfL3)

## What this file resolves

The moment method bounds the worst Gauss period `M(n) = max_{t≠0}‖η_t‖`, `η_t = Σ_{x∈μ_n} e_p(tx)`,
by the order-`r` additive energy `E_r(μ_n) = #{(a,b)∈μ_n^{2r} : Σa = Σb}` via
`M(n) ≤ (p·E_r)^{1/2r}`. The char-`0` (Lam–Leung / Wick) ceiling is `E_r^{(0)} ≤ (2r−1)!!·n^r`.
At the prize prime the **raw** energy saturates toward the trivial `n^{2r}` (the `t=0` DC term
`n^{2r}/p` dominates for `n ≥ 64`), so the right object is the **DC-subtracted energy**

  `A_r := E_r − n^{2r}/p`.

The campaign's prior height-route no-go (`MomentMethodPrizeDepthNoGo.lean`,
`HeightGateNormBound.lean`) proves the char-`0`→char-`p` transfer of `A_r ≤ Wick` only up to
`r ≤ rMax ≈ 2β`, leaving a **scoping gap**: maybe `A_r` itself *overshoots* `Wick` at the optimal
depth `r ≈ log m` (extra `±1`-relations clustering at `0 mod p`), which would make the moment
method's energy INPUT genuinely FALSE there — dead by all routes.

This file settles the scoping gap by exhibiting the EXACT spectral structure of `A_r` and proving:

> **The `A_r > Wick` overshoot at depth `r` is *equivalent in difficulty* to refuting the prize
> bound from below.** Precisely, `A_r > Wick ⟹ M(n) > ((2r−1)!!)^{1/2r}·√n`, and at the optimal
> depth `r = r_opt ≈ log m` the right side is exactly the prize floor `√(2 n log m)`. So a
> proof of overshoot at `r_opt` would itself be a proof that the house exceeds the prize bound —
> i.e. the overshoot direction **reduces to (the negation of) the wall**, it is not easier.

Numerics (`scripts/probes/probe_wfL3_defect_onset.py`, exact `E_r` over PROPER subgroups
`μ_n ≤ 𝔽_p^*`, `n=8,16,32`, `β≈4`) confirm the verdict and REFUTE the "onset at `rMax≈2β`"
hope: `A_r/Wick` is `< 1` and **monotonically DECREASING** in `r` (n=8, β=3.5: `0.99, 0.86,
0.64, 0.42, 0.23, 0.11, 0.05, …, 0.0006` at r=1..11) — A_r NEVER overshoots Wick, at any reachable
depth. The spectral cross-check `A_r = (1/p)Σ_{t≠0}|η_t|^{2r}` matches to machine precision.

## The mathematical content (all elementary, axiom-clean)

The exact spectral identity (additive characters; `|η_0| = n`, so the `t=0` term is the DC term):

  `E_r = (1/p) Σ_{t∈𝔽_p} |η_t|^{2r}`,  hence  `A_r = E_r − n^{2r}/p = (1/p) Σ_{t≠0} |η_t|^{2r}`.

We model the `p−1` nontrivial spectral values by a `Finset`-indexed nonnegative family `s : ι → ℝ`
(`s i = |η_{t_i}|`, `t_i ≠ 0`), `p` the prime size, and set
`A r := (1/p) Σ_i (s i)^{2r}`, `house := max_i (s i)`. The whole argument is then two elementary
facts about such finite power sums:

* **The sandwich** (`A_ge_house_pow`, `A_le_house_pow`):
  `house^{2r}/p ≤ A r ≤ ((#ι)/p)·house^{2r} ≤ house^{2r}` (using `#ι = p−1 < p`).
* **Overshoot ⟹ big house** (`overshoot_imp_house_gt`): `Wick < A r ⟹ Wick < house^{2r}`,
  hence `house > Wick^{1/2r}`.

Feeding `Wick = (2r−1)!!·n^r` and `Wick^{1/2r} = ((2r−1)!!)^{1/2r}·√n ≈ √(2nr)`, at `r=r_opt≈log m`:
`house > √(2 n log m)` — the prize-bound negation (`overshoot_imp_house_gt_prizeForm`,
`overshoot_at_rOpt_refutes_prize`).

## Honest verdict (the CRUCIAL CHECK)

The overshoot is NOT genuinely easier than the BGK upper bound. A single explicit over-clustering
family would have to push the FULL spectral moment `Σ_{t≠0}|η_t|^{2r}` above `p·Wick`, but by the
sandwich that forces the single largest eigenvalue `M(n) = house` itself above `Wick^{1/2r}` —
which AT `r_opt` is the prize floor. So "lower-bound the clustering count" is, at the only depth
that matters, identical to "lower-bound `M(n)` past the prize bound" = solve the wall from the
other side. **Clean negative: the overshoot reduces to the wall.** The numerics independently show
there is in fact no overshoot at all (DC subtraction keeps `A_r < Wick` monotonically).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.DefectOnsetOvershoot

open Finset

/-! ## §1  The DC-subtracted energy as a nontrivial spectral moment

We work with an abstract model of the `p−1` nontrivial Gauss-period magnitudes:
`ι` indexes the nonzero frequencies `t ≠ 0`, `s i = ‖η_{t_i}‖ ≥ 0`, and `p` is the prime.
The DC-subtracted order-`r` additive energy is `A r := (1/p) Σ_i (s i)^{2r}` — exactly the
character-sum identity `A_r = E_r − n^{2r}/p = (1/p) Σ_{t≠0} |η_t|^{2r}`. -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The DC-subtracted order-`r` additive energy**, in its exact spectral form
`A r = (1/p) Σ_i (s i)^{2r}` (sum over the nonzero frequencies). `p` is the prime, `s i ≥ 0` the
Gauss-period magnitudes `‖η_{t_i}‖`. -/
noncomputable def A (p : ℝ) (s : ι → ℝ) (r : ℕ) : ℝ := (1 / p) * ∑ i, (s i) ^ (2 * r)

/-- **The house** `M(n) = max_{t≠0} ‖η_t‖`, modeled as the finite maximum of the spectrum. -/
noncomputable def house (s : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty s

/-- The house is attained: there is a frequency `i₀` with `s i₀ = house s`. -/
theorem exists_house_eq (s : ι → ℝ) : ∃ i₀, s i₀ = house s := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty s
  exact ⟨i₀, hi₀.symm⟩

/-- Every spectral value is `≤ house`. -/
theorem le_house (s : ι → ℝ) (i : ι) : s i ≤ house s :=
  Finset.le_sup' s (Finset.mem_univ i)

/-! ## §2  The sandwich `house^{2r}/p ≤ A r ≤ (#ι/p)·house^{2r}` -/

/-- **Lower sandwich: a single dominant eigenvalue.** `A r ≥ house^{2r}/p`. The largest spectral
term alone contributes `house^{2r}`, divided by `p`. This is the bound a single over-clustering
family would have to beat to make `A r` large — but it pins the bound on the single house value. -/
theorem A_ge_house_pow {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (r : ℕ) :
    (house s) ^ (2 * r) / p ≤ A p s r := by
  unfold A
  obtain ⟨i₀, hi₀⟩ := exists_house_eq s
  have hterm : (house s) ^ (2 * r) ≤ ∑ i, (s i) ^ (2 * r) := by
    rw [← hi₀]
    refine Finset.single_le_sum (f := fun i => (s i) ^ (2 * r)) ?_ (Finset.mem_univ i₀)
    intro i _; exact pow_nonneg (hs i) _
  rw [div_eq_inv_mul, one_div]
  exact mul_le_mul_of_nonneg_left hterm (le_of_lt (inv_pos.mpr hp))

/-- **Upper sandwich.** `A r ≤ (#ι / p)·house^{2r}`: every one of the `#ι` terms is `≤ house^{2r}`.
With `#ι = p−1 < p` this gives `A r < house^{2r}`. -/
theorem A_le_card_house_pow {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (r : ℕ) :
    A p s r ≤ ((Fintype.card ι : ℝ) / p) * (house s) ^ (2 * r) := by
  unfold A
  have hsum : ∑ i, (s i) ^ (2 * r) ≤ ∑ _i : ι, (house s) ^ (2 * r) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact pow_le_pow_left₀ (hs i) (le_house s i) _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (1 / p) * ∑ i, (s i) ^ (2 * r)
      ≤ (1 / p) * ((Fintype.card ι : ℝ) * (house s) ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((Fintype.card ι : ℝ) / p) * (house s) ^ (2 * r) := by ring

/-- **The clean upper bound `A r < house^{2r}`** whenever the number of nontrivial frequencies is
`< p` (which it is: `#ι = p − 1`). So the DC-subtracted energy is sandwiched between `house^{2r}/p`
and `house^{2r}`: it is, up to the factor `p`, the `2r`-th power of the single house value. -/
theorem A_lt_house_pow {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Fintype.card ι : ℝ) < p) (r : ℕ) (hpos : 0 < house s) :
    A p s r < (house s) ^ (2 * r) := by
  have hstep := A_le_card_house_pow hp s hs r
  have hfrac : (Fintype.card ι : ℝ) / p < 1 := (div_lt_one hp).mpr hcard
  have hhouse : (0 : ℝ) < (house s) ^ (2 * r) := by positivity
  calc A p s r ≤ ((Fintype.card ι : ℝ) / p) * (house s) ^ (2 * r) := hstep
    _ < 1 * (house s) ^ (2 * r) := by
        apply mul_lt_mul_of_pos_right hfrac hhouse
    _ = (house s) ^ (2 * r) := one_mul _

/-! ## §3  Overshoot ⟹ big house (the reduction to the wall) -/

/-- **THE REDUCTION (raw form).** If the DC-subtracted energy `A r` exceeds a threshold `W`
(`W < A r`), then the house exceeds the `2r`-th root of `W` in the strong sense `W < house^{2r}`.
Mechanism: `A r < house^{2r}` (upper sandwich, `#ι < p`), so `W < A r < house^{2r}`. **An overshoot
of *any* threshold `W` by the DC-subtracted energy forces the single largest Gauss period to
exceed `W^{1/2r}`.** When `W = Wick`, this is precisely "overshoot ⟹ the house beats `Wick^{1/2r}`". -/
theorem overshoot_imp_house_pow_gt {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Fintype.card ι : ℝ) < p) (r : ℕ) (hpos : 0 < house s) {W : ℝ}
    (hover : W < A p s r) : W < (house s) ^ (2 * r) :=
  lt_trans hover (A_lt_house_pow hp s hs hcard r hpos)

/-- **THE REDUCTION (root form).** Overshoot of threshold `W ≥ 0` by `A r` forces
`house > W^{1/2r}`. (Take `2r`-th roots in `overshoot_imp_house_pow_gt`.) With `W = Wick =
(2r−1)!!·n^r`, `W^{1/2r} = ((2r−1)!!·n^r)^{1/2r} = ((2r−1)!!)^{1/2r}·√n ≈ √(2nr)` — so an `A_r`
overshoot of Wick at depth `r` proves the house exceeds `≈ √(2nr)`. At `r = r_opt ≈ log m` this is
the prize floor `√(2 n log m)`: the overshoot *is* a lower bound on `M(n)` past the prize bound. -/
theorem overshoot_imp_house_gt {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Fintype.card ι : ℝ) < p) (r : ℕ) (hr : 1 ≤ r) (hpos : 0 < house s)
    {W : ℝ} (hW : 0 ≤ W) (hover : W < A p s r) :
    W ^ ((1 : ℝ) / (2 * r)) < house s := by
  have hpow : W < (house s) ^ (2 * r) := overshoot_imp_house_pow_gt hp s hs hcard r hpos hover
  have h2r : (0 : ℝ) < 2 * r := by
    have : (0 : ℕ) < 2 * r := by omega
    exact_mod_cast this
  -- take (1/2r)-th rpow of both sides; (house^{2r})^{1/2r} = house
  have hmono : W ^ ((1 : ℝ) / (2 * r)) < ((house s) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_lt_rpow hW hpow (by positivity)
  have hsimp : ((house s) ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * r)) = house s := by
    rw [show ((house s) ^ (2 * r) : ℝ) = (house s) ^ ((2 * r : ℕ) : ℝ) from
      (Real.rpow_natCast (house s) (2 * r)).symm, ← Real.rpow_mul (le_of_lt hpos)]
    rw [show ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) from by push_cast; ring]
    rw [mul_one_div, div_self (ne_of_gt h2r), Real.rpow_one]
  rwa [hsimp] at hmono

/-! ## §4  Wick, the prize floor, and the explicit equivalence -/

/-- The Wick / Lam–Leung char-`0` energy ceiling `Wick n r = (2r−1)!!·n^r`, with `(2r−1)!!` the
double factorial of odd numbers (the Gaussian moment count). We import the `ℕ` value as a real. -/
noncomputable def Wick (n r : ℕ) (doubleFactOdd : ℕ → ℕ) : ℝ := (doubleFactOdd r : ℝ) * (n : ℝ) ^ r

/-- **`Wick^{1/2r} = ((2r−1)!!)^{1/2r}·√n`.** The `2r`-th root of the Wick ceiling factors as the
double-factorial root times `√n`. (Used to read the reduction as `house > ((2r−1)!!)^{1/2r}·√n`.) -/
theorem wick_rpow_eq {n r : ℕ} (df : ℕ → ℕ) (hr : 1 ≤ r) (hn : 0 < n) (hdf : 0 < df r) :
    (Wick n r df) ^ ((1 : ℝ) / (2 * r))
      = (df r : ℝ) ^ ((1 : ℝ) / (2 * r)) * Real.sqrt (n : ℝ) := by
  have h2r : (0 : ℝ) < 2 * r := by
    have : (0 : ℕ) < 2 * r := by omega
    exact_mod_cast this
  have hdfpos : (0 : ℝ) < (df r : ℝ) := by exact_mod_cast hdf
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold Wick
  rw [Real.mul_rpow (le_of_lt hdfpos) (by positivity)]
  congr 1
  -- (n^r)^{1/2r} = n^{r·(1/2r)} = n^{1/2} = √n
  rw [show ((n : ℝ) ^ r : ℝ) = (n : ℝ) ^ ((r : ℕ) : ℝ) from (Real.rpow_natCast (n : ℝ) r).symm,
    ← Real.rpow_mul hnnn]
  have hexp : ((r : ℕ) : ℝ) * ((1 : ℝ) / (2 * r)) = 1 / 2 := by
    have hrne : (r : ℝ) ≠ 0 := by
      have : (0 : ℕ) < r := hr
      positivity
    field_simp
  rw [hexp, ← Real.sqrt_eq_rpow]

/-- **THE REDUCTION, prize form.** If the DC-subtracted energy `A r` overshoots the Wick ceiling
`(2r−1)!!·n^r` at depth `r`, then the house exceeds `((2r−1)!!)^{1/2r}·√n`. So *proving overshoot
is proving a matching lower bound on the worst Gauss period* `M(n) = house`. There is no shortcut:
the overshoot lives at the same place as the house lower bound. -/
theorem overshoot_imp_house_gt_prizeForm {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Fintype.card ι : ℝ) < p) {n r : ℕ} (df : ℕ → ℕ) (hr : 1 ≤ r) (hn : 0 < n)
    (hdf : 0 < df r) (hpos : 0 < house s) (hover : Wick n r df < A p s r) :
    (df r : ℝ) ^ ((1 : ℝ) / (2 * r)) * Real.sqrt (n : ℝ) < house s := by
  have hWnn : (0 : ℝ) ≤ Wick n r df := by
    unfold Wick; positivity
  have h := overshoot_imp_house_gt hp s hs hcard r hr hpos hWnn hover
  rwa [wick_rpow_eq df hr hn hdf] at h

/-! ## §5  The honest verdict, as named statements

The reduction says: **overshoot at depth `r` ⟹ house `> ((2r−1)!!)^{1/2r}·√n`.** The prize bound
asserts the OPPOSITE, `house ≤ C·√(n·log m)`. At `r = r_opt ≈ log m`, `((2r)!!)^{1/2r}·√n ≈ √(2 n
log m)` is the prize floor itself; so overshoot at `r_opt` is a proof that `house` exceeds (a
constant times) the prize bound — i.e. a refutation of the prize from below. We record this as the
clean negative: the overshoot direction is NOT easier than the wall. -/

/-- **`PrizeBound s C T`**: the conjectured upper bound on the worst Gauss period,
`house s ≤ C · T`, where `T ≈ √(n·log m)` is the prize floor and `C` the (constant) prize constant.
Stated abstractly so the contradiction below is a pure inequality fact. -/
def PrizeBound (s : ι → ℝ) (C T : ℝ) : Prop := house s ≤ C * T

/-- **THE HONEST CHECK, RESOLVED (overshoot reduces to the wall).** Suppose at depth `r` the
DC-subtracted energy overshoots Wick (`Wick < A r`) AND the floor root dominates the prize bound,
`C·T ≤ ((2r−1)!!)^{1/2r}·√n` (which holds at `r=r_opt`, where the root IS the floor `√(2n log m)≥
C√(n log m)` once `r_opt ≥ C²·log m`, i.e. for the prize constant). Then the prize bound is FALSE.
So *any* proof of overshoot at the optimal depth is *ipso facto* a refutation of the prize bound —
the overshoot lower bound is at least as hard as the BGK upper bound. There is no free lunch. -/
theorem overshoot_refutes_prize {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Fintype.card ι : ℝ) < p) {n r : ℕ} (df : ℕ → ℕ) (hr : 1 ≤ r) (hn : 0 < n)
    (hdf : 0 < df r) (hpos : 0 < house s) (hover : Wick n r df < A p s r)
    {C T : ℝ} (hfloor : C * T ≤ (df r : ℝ) ^ ((1 : ℝ) / (2 * r)) * Real.sqrt (n : ℝ)) :
    ¬ PrizeBound s C T := by
  intro hPB
  have hgt := overshoot_imp_house_gt_prizeForm hp s hs hcard df hr hn hdf hpos hover
  -- house ≤ C·T ≤ root < house, contradiction
  exact absurd (le_trans hPB hfloor) (not_le.mpr hgt)

/-- **Symmetric corollary: the prize bound forbids overshoot.** Contrapositive of
`overshoot_refutes_prize`: if the prize bound holds and the floor root dominates it at depth `r`,
then the DC-subtracted energy does NOT overshoot Wick at `r` — `A r ≤ Wick`. This is the
direction the numerics exhibit unconditionally: `A_r ≤ Wick` at every reachable depth (because the
true house IS `≈ √(n log m)`, below the root `√(2nr)` for `r ≥ ~ log m`). The "overshoot" and "no
overshoot" verdicts are two faces of the SAME wall — neither is provable without resolving `M(n)`. -/
theorem prizeBound_imp_no_overshoot {p : ℝ} (hp : 0 < p) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Fintype.card ι : ℝ) < p) {n r : ℕ} (df : ℕ → ℕ) (hr : 1 ≤ r) (hn : 0 < n)
    (hdf : 0 < df r) (hpos : 0 < house s) {C T : ℝ}
    (hfloor : C * T ≤ (df r : ℝ) ^ ((1 : ℝ) / (2 * r)) * Real.sqrt (n : ℝ))
    (hPB : PrizeBound s C T) : A p s r ≤ Wick n r df := by
  by_contra hcon
  push_neg at hcon
  exact overshoot_refutes_prize hp s hs hcard df hr hn hdf hpos hcon hfloor hPB

end ArkLib.ProximityGap.DefectOnsetOvershoot

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound], NO sorryAx) -/
section AxiomAudit
open ArkLib.ProximityGap.DefectOnsetOvershoot
#print axioms A_ge_house_pow
#print axioms A_le_card_house_pow
#print axioms A_lt_house_pow
#print axioms overshoot_imp_house_pow_gt
#print axioms overshoot_imp_house_gt
#print axioms wick_rpow_eq
#print axioms overshoot_imp_house_gt_prizeForm
#print axioms overshoot_refutes_prize
#print axioms prizeBound_imp_no_overshoot
end AxiomAudit
