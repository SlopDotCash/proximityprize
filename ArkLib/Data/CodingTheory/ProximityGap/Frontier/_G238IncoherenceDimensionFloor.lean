/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G233JacobiL2MassFloorNoGo
import Mathlib.Algebra.Order.Chebyshev

/-!
# G238: the incoherence dimension floor — no bounded eigen-subfamily recovers the fanout (#466)

The quotient-Jacobi coordinate system is closed to compression in the *coordinate* sense (G228/G229/
G231: no fixed arithmetic subfamily) and, empirically, in the *spectral* sense (G232: the covariance
vector `S` is diffuse over `Ω(m)` Gram-eigen-directions and avoids the large-eigenvalue subspace, so
recovering a constant fraction of `‖S‖²` needs a positive fraction of the full family — `≈ m/2`
directions for 90% recovery in every sponsor cell).  G232 is an exact numerical measurement; this
file is its **theorem-level calibrated consumer** — the basis-independent invariant that turns the
measured diffuseness into a genuine dimension floor.

The mechanism is pure finite-dimensional linear algebra, *no character theory and no spectral
hypothesis*.  Fix any orthonormal-style expansion of the target vector into directions `i ∈ Ω` with
per-direction energies `energy i = |⟨S, vᵢ⟩|²` and total `‖S‖² = ∑_{i ∈ Ω} energy i`.  G232 measures
the single decisive structural fact: every individual direction carries only a small fraction of the
total, `energy i ≤ ρ · ‖S‖²`.  There are two regimes of `ρ`, and they prove two *different*
strengths of floor — kept distinct here to avoid overstating what a constant cap gives:

* **(Recovery ceiling.)**  Any `k`-direction subfamily recovers at most `k · ρ · ‖S‖²` of the
  energy: a coherent combination over `≤ k` directions cannot capture more than its dimension times
  the per-direction cap.

* **(Dimension floor — the operative contrapositive.)**  To recover a fraction `f` of `‖S‖²`
  (i.e. `f · ‖S‖² ≤` the subfamily energy) one needs at least `f / ρ` directions: `k ≥ f / ρ`.

* **(Constant cap `ρ = 1/4`.)**  G232's *worst-single-direction* measurement (top-`S`-energy
  direction ≤ ~24%, `λ_max` direction 4–7%) gives an `m`-independent `ρ ≤ 1/4`.  This yields only a
  *constant* floor: `k ≥ f/ρ`, e.g. `k ≥ 18/5 > 3` for `f = 9/10`.  It rules out every `O(1)`
  coherent eigen-combination of dimension *below* `f/ρ` (in particular no 3-direction combination
  recovers 90%), but it does **not**, by itself, force `Ω(m)` — a constant cap can only ever give a
  constant floor.

* **(Diffuse cap `ρ = c/m` — the source of `Ω(m)`.)**  G232's *global diffuseness* measurement is
  the stronger fact: the energy is spread over `Ω(m)` directions, i.e. each carries only
  `energy i ≤ (c/m) · ‖S‖²` for an `m`-independent `c`.  Feeding this `m`-*scaled* cap into the same
  dimension floor gives `k ≥ f/ρ = (f/c) · m = Ω(m)` — reproducing G232's `≈ m/2`-for-90%
  measurement.  This is the honest `Ω(m)` statement: it requires the `1/m`-decaying cap, not the
  constant one.  No `O(1)`- or `O(polylog)`-dimensional coherent eigen-combination carries a
  constant fraction of `S`.

This upgrades G231 from "no fixed *coordinate* subfamily" to "no *coherent eigen-subfamily* either":
the quotient-Jacobi fanout is basis-independent.  It is a guardrail/no-go — it does **not** consume
the prize target, does not weaken BGK/Paley, and formalizes no new character-sum estimate.  Its
worth is theorem-level: it forecloses the last dimensional-reduction hope (replacing the full
quotient-Jacobi family with a bounded coherent eigen-combination strictly weaker than the BGK
packet) that the coordinate-subset fences G228/G229/G231 do not by themselves rule out.  CORE
remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G238IncoherenceDimensionFloor

open Finset

variable {ι : Type*}

/-! ## The recovery ceiling: a `k`-direction subfamily recovers `≤ k · ρ · total` -/

/-- **Incoherence recovery ceiling (abstract).**

Let `energy : ι → ℝ` assign a nonnegative energy to each direction and let `total` be the full
energy `‖S‖²`.  Suppose every direction obeys the per-direction cap `energy i ≤ rho * total`
(`hcap`).  Then any finite subfamily `K : Finset ι` recovers at most `#K · rho · total`:

```text
∑_{i ∈ K} energy i ≤ #K · (rho · total).
```

This is the exact statement that a coherent linear combination supported on `#K` directions cannot
capture more than its dimension times the per-direction cap.  Pure `Finset.sum_le_sum` + constant
sum; no orthogonality, no spectral structure. -/
theorem recovery_ceiling (K : Finset ι) (energy : ι → ℝ) (total rho : ℝ)
    (hcap : ∀ i ∈ K, energy i ≤ rho * total) :
    ∑ i ∈ K, energy i ≤ (K.card : ℝ) * (rho * total) := by
  calc ∑ i ∈ K, energy i
      ≤ ∑ _i ∈ K, rho * total := Finset.sum_le_sum hcap
    _ = (K.card : ℝ) * (rho * total) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The dimension floor: recovering a fraction `f` forces `k ≥ f / rho` directions -/

/-- **Incoherence dimension floor (operative contrapositive).**

Under the per-direction cap `energy i ≤ rho * total` on the recovered subfamily `K`, if that
subfamily recovers at least a fraction `f` of the total energy — `f * total ≤ ∑_{i ∈ K} energy i` —
and `rho > 0`, then the subfamily must contain at least `f / rho` directions:

```text
f / rho ≤ #K.
```

Contrapositive of `recovery_ceiling`: `f * total ≤ #K * rho * total` divided through by
`rho * total`.  The strength of the floor depends entirely on how `rho` scales: a *constant* cap
(e.g. G232's `rho ≤ 1/4`) gives only a *constant* floor `#K ≥ f / rho`, while the *diffuse* cap
`rho = c / m` gives the linear floor `#K ≥ (f/c)·m = Ω(m)` — see `diffuse_dimension_floor`.  This
abstract statement proves neither; it delivers exactly `f / rho ≤ #K`, and the caller supplies the
regime of `rho`. -/
theorem dimension_floor (K : Finset ι) (energy : ι → ℝ) (total rho f : ℝ)
    (htot : 0 < total) (hrho : 0 < rho)
    (hcap : ∀ i ∈ K, energy i ≤ rho * total)
    (hrec : f * total ≤ ∑ i ∈ K, energy i) :
    f / rho ≤ (K.card : ℝ) := by
  have hceil : ∑ i ∈ K, energy i ≤ (K.card : ℝ) * (rho * total) :=
    recovery_ceiling K energy total rho hcap
  -- f * total ≤ #K * (rho * total)
  have hchain : f * total ≤ (K.card : ℝ) * (rho * total) := hrec.trans hceil
  -- cancel the positive `total`, then the positive `rho`.
  have hchain' : f * total ≤ ((K.card : ℝ) * rho) * total := by
    calc f * total ≤ (K.card : ℝ) * (rho * total) := hchain
      _ = ((K.card : ℝ) * rho) * total := by ring
  have hf_le : f ≤ (K.card : ℝ) * rho := le_of_mul_le_mul_right hchain' htot
  rw [div_le_iff₀ hrho]
  exact hf_le

/-! ## Calibrated instance: G232's constant cap `rho ≤ 1/4` forces `> 3` directions for 90% -/

/-- **G232-calibrated dimension floor (constant cap — CONSTANT floor only).**

Specialise `dimension_floor` to G232's *worst-single-direction* constant: the per-direction energy
cap `rho = 1/4` (the top-`S`-energy direction never exceeds ~24% of `‖S‖²` in any sponsor cell) and
the target recovery fraction `f = 9/10` (90% energy recovery).  Then any subfamily `K` achieving
90% recovery satisfies

```text
18 / 5 ≤ #K,   hence   4 ≤ #K   (a strict `> 3` floor).
```

This is an `m`-*independent* floor: it rules out every `O(1)` coherent eigen-combination of
dimension below `18/5` (no three-direction combination recovers 90% of `S`); but a constant cap
gives only a constant floor — it does NOT by itself force `Ω(m)`.  The `Ω(m)` statement needs the
diffuse
`1/m`-decaying cap; see `diffuse_dimension_floor` below. -/
theorem g232_calibrated_floor (K : Finset ι) (energy : ι → ℝ) (total : ℝ)
    (htot : 0 < total)
    (hcap : ∀ i ∈ K, energy i ≤ (1 / 4 : ℝ) * total)
    (hrec : (9 / 10 : ℝ) * total ≤ ∑ i ∈ K, energy i) :
    (18 / 5 : ℝ) ≤ (K.card : ℝ) := by
  have h := dimension_floor K energy total (1 / 4 : ℝ) (9 / 10 : ℝ) htot (by norm_num) hcap hrec
  -- (9/10) / (1/4) = 18/5
  have heq : (9 / 10 : ℝ) / (1 / 4 : ℝ) = (18 / 5 : ℝ) := by norm_num
  rwa [heq] at h

/-- **Integer dimension floor from the G232 calibration.**  Since `18/5 > 3`, the calibrated
recovery bound forces a *strict* `#K ≥ 4`: no three-direction coherent eigen-combination recovers
90% of `S`. -/
theorem g232_calibrated_card_ge_four (K : Finset ι) (energy : ι → ℝ) (total : ℝ)
    (htot : 0 < total)
    (hcap : ∀ i ∈ K, energy i ≤ (1 / 4 : ℝ) * total)
    (hrec : (9 / 10 : ℝ) * total ≤ ∑ i ∈ K, energy i) :
    4 ≤ K.card := by
  have h : (18 / 5 : ℝ) ≤ (K.card : ℝ) := g232_calibrated_floor K energy total htot hcap hrec
  -- 18/5 = 3.6 ≤ #K, and #K is an integer, so 4 ≤ #K.
  have h3 : (3 : ℝ) < (K.card : ℝ) := by linarith
  have : 3 < K.card := by exact_mod_cast h3
  omega

/-! ## The diffuse `Ω(m)` floor: an `m`-scaled cap `rho = c/m` forces `≥ (f/c)·m` directions -/

/-- **Diffuse dimension floor (`Ω(m)` — the honest source of the linear growth).**

The constant cap `rho = 1/4` above only gives a constant floor.  The `Ω(m)` statement rests on
G232's *global diffuseness* measurement: the energy is spread so that each direction carries only an
`O(1/m)` share, `energy i ≤ (c / m) · total` for an `m`-independent constant `c > 0`.  Feeding this
`m`-scaled cap into `dimension_floor` gives a floor that grows *linearly* in `m`:

```text
rho = c / m,   f / rho = (f / c) · m ≤ #K.
```

So recovering a constant fraction `f` of `‖S‖²` forces `#K ≥ (f/c)·m = Ω(m)` directions — exactly
G232's `≈ m/2`-for-90% measurement, with `c` the empirical diffuseness constant.  This is the honest
`Ω(m)` incoherence floor: no `O(1)`- or `O(polylog)`-dimensional coherent eigen-combination carries
a constant fraction of `S`.  It requires the decaying cap; the constant-cap corollary above does
not imply it. -/
theorem diffuse_dimension_floor (K : Finset ι) (energy : ι → ℝ) (total c f : ℝ) (m : ℕ)
    (htot : 0 < total) (hc : 0 < c) (hm : 0 < m)
    (hcap : ∀ i ∈ K, energy i ≤ (c / (m : ℝ)) * total)
    (hrec : f * total ≤ ∑ i ∈ K, energy i) :
    (f / c) * (m : ℝ) ≤ (K.card : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrho : (0 : ℝ) < c / (m : ℝ) := div_pos hc hmR
  have h := dimension_floor K energy total (c / (m : ℝ)) f htot hrho hcap hrec
  -- f / (c/m) = (f/c) * m
  have heq : f / (c / (m : ℝ)) = (f / c) * (m : ℝ) := by
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm, mul_div_assoc]
  rwa [heq] at h

end ArkLib.ProximityGap.Frontier.G238IncoherenceDimensionFloor
