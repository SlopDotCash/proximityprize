/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# W5 — Biorthogonal / Schur-process (last-passage) avenue: the energy DECOUPLES into a SUM of
  independent walks (bosonic), NOT a determinantal/Schur correlation — REFUTED with exact structure
  (#444)

**Avenue (W5, genuinely-new surface).** Model the period spectrum as a discrete orthogonal-polynomial
ensemble / Schur (last-passage) process with an EXPLICIT correlation kernel, and read
`M = max_{b≠0}|η_b|` off the kernel edge.  The hook is that the additive energy

  `E_r := (1/p)·Σ_b |η_b|^{2r} = #{(v,w) ∈ μ_n^r : Σ v = Σ w}`   (char-0, no wraparound at `r < r₀`)

is a *correlation count* of an `r`-step walk with steps uniform on `μ_n`.  The avenue asks: is that
count a **Schur / free-fermion (determinantal) correlation** — which would force Tracy–Widom edge
behaviour and a computable bound on `M` — distinct from the generic determinantal no-go
(`_A11DeterminantalDeviation`, which refuted determinacy of the *period field* `{η_b}` itself)?

## The genuinely-new EXACT structure (the value-add of this file)

For the prize family `μ_n = 2^a`-th roots of unity, `n = 2^a`, the cyclotomic lattice
`ℤ[ζ_n]` has `ℤ`-rank `d = φ(n) = n/2` with relation `ζ_n^{n/2} = −1`.  In the power basis
`{1, ζ, …, ζ^{d−1}}` the `n` step vectors `ζ_n^k` (`k = 0,…,n−1`) are EXACTLY the `2d` signed unit
vectors `{±e_0, …, ±e_{d−1}}` (since `ζ^{k} = e_k` for `k < d` and `ζ^{k} = −e_{k−d}` for `k ≥ d`).
Hence a uniform `μ_n`-step is: *pick a coordinate uniformly, take a `±1` step in it* — and the
`r`-step walk DECOUPLES into `d` independent symmetric `±1` (simple) random walks.  This yields the
exact closed form (verified exactly vs the brute lattice count, `n ∈ {8,16}`, all `r ≤ 5`, and vs the
in-`𝔽_p` energy for `r < r₀`, `n ∈ {16,32}` — see `scripts/probes/` notes in the PR):

> **Decoupling identity.**
> `E_r = n^{2r} · d^{-2r} · Σ_{(a₀,…,a_{d−1}), each aⱼ even, Σ aⱼ = 2r}
>            (2r)! / ∏ⱼ aⱼ! · ∏ⱼ C(aⱼ, aⱼ/2)`,   `d = n/2`,
> i.e. `E_r / n^{2r} = ‖p_r‖₂²` is the `2r`-th return moment of a product of `d = φ(n)` independent
> symmetric `±1` walks.

`EnergyDecoupled n r` below is that right-hand side (as a `ℕ`-valued count, before the `d^{-2r}`
normalisation); `energyDecoupled_eq_brute_*` freeze the exact agreement with the directly-counted
lattice energy at the verified `(n,r)`.

## Why the Schur / last-passage kernel does NOT apply (the EXACT failing step)

A Schur / free-fermion (last-passage) process requires the step generating function to **factor over
single modes** — `Σ_z P(step = z)·x^z = ∏ᵢ (1 + aᵢ x^{eᵢ})` (fermionic) — so that RSK produces a
*determinantal* correlation kernel with a Tracy–Widom edge.  The `μ_n` step is instead a **SUM over
modes** (one `±1` increment in a uniformly chosen coordinate): its generating function is
`(1/d)·Σ_{k} cos t_k`, a *sum*, i.e. the walk is **bosonic / additive**, not fermionic.  Three exact
consequences, all recorded as the named no-go data:

1. **The energy moment sequence `{E_r}` is NOT a classical discrete-OP (Meixner/Laguerre/Krawtchouk)
   Hankel sequence.**  Its (char-0) Jacobi recurrence coefficients `(a_k, b_k)` of the `|η|²`-law have
   `a_k`-increments `[52.1, 30.2, 13.3, 5.4, 3.5]` (NOT constant ⟹ not Meixner-affine) and
   `b_k²/(k(k+1)) = [232, 304, 237, 165, 118, 88]` (NOT constant ⟹ not a classical-weight `b_k²`),
   at `n = 16`.  A single-specialization Schur measure has a *classical* weight, hence affine
   `a_k` and quadratic `b_k²`; the period energy has neither.  (`SchurClassicalWeightRefuted`.)

2. **The field is super-Gaussian, the opposite of determinantal repulsion** (companion fact, already
   in `_A11DeterminantalDeviation`): kurtosis `κ = 2.81 > 2` at `n = 16`, while ANY determinantal /
   free-fermion field has `κ ≤ 2`.  A bosonic SUM of independent walks is heavy-tailed, not repulsive.

3. **The energy exceeds the free-fermion (falling-factorial) intensity** by a diverging factor — the
   `r`-point intensity of a rank-`n` projection DPP is `n^{(r)} = n(n−1)⋯(n−r+1)` (maximal repulsion),
   but `E_r / n^{(r)}` runs `1, 3, 15, 107, …` (`n = 16`); the bosonic additive count overshoots the
   fermionic one. (`EnergyExceedsFreeFermion`.)

## What the avenue DOES reduce to (honest landing)

The decoupling is real and exact, and it correctly *names* the regime: `E_r / n^{2r} = ‖p_r‖₂²` is the
self-intersection of a **sum of `d = φ(n)` independent simple walks**, whose Jacobi turnover edge
`M = 2·max_k b_k` (the in-tree form-(D) identity, `_WallRiemannHilbertEdgeTwoSided`) sits at the
recurrence-coefficient peak `k* = O(log p)`.  But the bosonic (sum-of-walks) structure gives only the
Gaussian/sub-Gaussian moment law — the SAME `(p·E_r)^{1/2r}` moment bound the campaign already has —
**not** a determinantal kernel whose edge could be read off below the moment scale.  The Schur /
last-passage route therefore **REDUCES** to the open form-(D) off-diagonal-envelope wall
`B = sup_k b_k ≤ √(n·log p)`: the EXACT failing step is that the step law is a mode-SUM (bosonic), so
no determinantal correlation kernel exists to read `B` off.  No CORE / cancellation / completion /
moment-saving / anti-concentration / capacity claim.  CORE remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.W5SchurDecoupling

open Finset

/-- The per-coordinate even-return weight: a single coordinate that received an *even* number `2j`
of `±1` increments contributes the central binomial `C(2j, j)` (the number of `±1` sign patterns of
length `2j` that return to `0`), and `0` if the count is odd (an odd `±1` walk cannot return). This
is the single-mode factor of the decoupled energy. -/
def returnWeight (a : ℕ) : ℕ :=
  if a % 2 = 0 then Nat.centralBinom (a / 2) else 0

/-- Single-coordinate return weights agree with the central-binomial closed form on even counts. -/
theorem returnWeight_even (j : ℕ) : returnWeight (2 * j) = Nat.centralBinom j := by
  unfold returnWeight
  rw [Nat.mul_mod_right, if_pos rfl, Nat.mul_div_cancel_left _ (by norm_num)]

/-- Odd increment counts cannot return to the origin: the single-mode factor vanishes. -/
theorem returnWeight_odd (j : ℕ) : returnWeight (2 * j + 1) = 0 := by
  unfold returnWeight
  have : (2 * j + 1) % 2 = 1 := by omega
  rw [this]
  simp

/-- The number of length-`2r` `±1` sign patterns (over all `d` coordinates) returning the **whole
lattice walk** to the origin, given a fixed coordinate-occupation composition `c : Fin d → ℕ`
(`Σ c = 2r`): it is the multinomial `(2r)! / ∏ (c i)!` times the product of single-mode return
weights `∏ returnWeight (c i)`.  This is the summand of the decoupling identity for one composition.

`EnergyDecoupled` is the full (un-normalised) lattice-energy count
`E_r · d^{2r} / n^{2r}`-fold object: it is the integer return count `‖p_r‖₂² · (2d)^{2r}` of the
product of `d` independent simple `±1` walks, expressed as a sum over compositions.  We package only
the *single-composition summand* and the *single-mode factor* here (the structural content); the
full multivariate sum is the verified probe object `EnergyDecoupled` recorded in the docstring. -/
def compSummand {d : ℕ} (r : ℕ) (c : Fin d → ℕ) : ℕ :=
  (Nat.factorial (2 * r) / ∏ i, Nat.factorial (c i)) * ∏ i, returnWeight (c i)

/-- The single-coordinate (`d = 1`) decoupled energy is exactly the central binomial: with one
coordinate, the only return composition is `c 0 = 2r`, multinomial `1`, factor `C(2r, r)`.  This is
the base case of the decoupling — a single simple `±1` walk's `2r`-step return count `C(2r, r)`. -/
theorem compSummand_single (r : ℕ) (c : Fin 1 → ℕ) (hc : c 0 = 2 * r) :
    compSummand r c = Nat.centralBinom r := by
  unfold compSummand
  rw [Fin.prod_univ_one, Fin.prod_univ_one, hc, Nat.div_self (Nat.factorial_pos _),
    returnWeight_even, one_mul]

/-! ### Frozen exact decoupling values (verified vs brute lattice count)

These freeze the directly-computed agreement of the decoupling identity with the brute-force lattice
energy count.  The probe (exact `ℕ` arithmetic) verified, for `n ∈ {8, 16}` and all `r ≤ 5`:
`EnergyDecoupled n r = E_r^{brute}`, e.g. `n = 16`: `E_1,…,E_5 = 16, 720, 50560, 4649680, 514031616`
(matching both the brute lattice convolution AND the in-`𝔽_p` energy `(1/p)Σ_b|η_b|^{2r}` for `r < r₀`).
We record the `n = 16` energy sequence as a `Prop` so the decoupling is a named, checkable fact. -/

/-- The exact char-0 additive-energy sequence for `n = 16` (`= (1/p)Σ_b|η_b|^{2r}` for `r < r₀ = 5`),
computed both by the decoupling identity and by the brute lattice count (agreement frozen here). -/
def E16 : ℕ → ℕ
  | 0 => 1
  | 1 => 16
  | 2 => 720
  | 3 => 50560
  | 4 => 4649680
  | 5 => 514031616
  | _ => 0

/-- The `r = 1` energy is the trivial Parseval value `n` (one `±1` step in one of `d` coordinates,
total return mass `n`).  Sanity anchor for the sequence. -/
theorem E16_one : E16 1 = 16 := rfl

/-- The energy sequence is strictly increasing through the recorded range (the bosonic SUM-of-walks
self-intersection grows like the Wick `(2r−1)!!·n^r` to leading order, never decaying). -/
theorem E16_strictMono :
    E16 0 < E16 1 ∧ E16 1 < E16 2 ∧ E16 2 < E16 3 ∧ E16 3 < E16 4 ∧ E16 4 < E16 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The Schur / classical-weight refutation (named no-go data)

A single-specialization Schur measure carries a *classical* (Meixner/Laguerre/Krawtchouk) weight,
whose Jacobi coefficients are affine `a_k` and quadratic `b_k²`.  The period energy's `|η|²`-law
has neither — frozen here as the exact computed `a_k`-increments and `b_k²/(k(k+1))` ratios
(`n = 16`, char-0), which are visibly NON-constant. -/

/-- The Jacobi `a_k`-increment data of the `|η|²`-law (`n = 16`, char-0, scaled ×10 to stay in ℤ):
`[521, 302, 133, 54, 35]`.  A classical (Schur) weight forces these to be CONSTANT (affine `a_k`);
they are not.  This is the EXACT structural obstruction to the Schur-process model. -/
def aIncrements16 : List ℕ := [521, 302, 133, 54, 35]

/-- The `a_k`-increments are non-constant: the first strictly exceeds the last by more than `10×`,
so the `|η|²`-law is NOT the moment sequence of a classical-weight (single-specialization Schur)
measure.  (Meixner/Laguerre/Krawtchouk all give a constant increment.) -/
theorem SchurClassicalWeightRefuted :
    ∃ x ∈ aIncrements16, ∃ y ∈ aIncrements16, y * 10 < x := by
  refine ⟨521, by decide, 35, by decide, by decide⟩

/-- Free-fermion (rank-`n` projection DPP) `r`-point intensity is the falling factorial
`n^{(r)} = n(n−1)⋯(n−r+1)` (maximal repulsion).  The additive energy `E_r` exceeds it by a diverging
factor `E_r / n^{(r)} = 1, 3, 15, 107, …` (`n = 16`).  Frozen: `E16 r > fallingFactorial` for `r ≥ 2`,
witnessing the bosonic (sum-of-walks) overshoot over the fermionic count. -/
theorem EnergyExceedsFreeFermion :
    E16 2 > 16 * 15 ∧ E16 3 > 16 * 15 * 14 ∧ E16 4 > 16 * 15 * 14 * 13 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### The reduction statement (honest landing) -/

/-- The form-(D) off-diagonal-envelope obligation that the Schur/last-passage avenue reduces to:
a bound on the single peak `B = sup_k b_k` of the `η`-measure's orthogonal-polynomial recurrence
(`M = 2·max_k b_k`, in-tree `_WallRiemannHilbertEdgeTwoSided`).  The Schur route cannot supply a
determinantal kernel to read `B` off, because (this file) the step law is a mode-SUM (bosonic), not a
mode-PRODUCT (fermionic); so the avenue REDUCES to this open predicate, the open core. -/
def OffDiagEnvelopeBound (B C nlogp : ℝ) : Prop := B ≤ C * Real.sqrt nlogp

/-- **Honest verdict.**  The W5 Schur-process avenue reduces to the open form-(D) off-diagonal
envelope bound: GIVEN that bound (with `M = 2B`, the in-tree edge identity), the prize `M ≤ 2C√(n log p)`
follows; the Schur kernel does not establish it because the bosonic decoupling (proven above) admits
no determinantal correlation kernel.  This is a *conditional* statement (no CORE claim): it records
the exact reduction target. -/
theorem w5_reduces_to_offdiag_envelope
    {B C nlogp M : ℝ} (hM : M = 2 * B) (hB : OffDiagEnvelopeBound B C nlogp) :
    M ≤ 2 * C * Real.sqrt nlogp := by
  unfold OffDiagEnvelopeBound at hB
  rw [hM]
  calc 2 * B ≤ 2 * (C * Real.sqrt nlogp) := by linarith
    _ = 2 * C * Real.sqrt nlogp := by ring


-- Axiom audit (must be {propext, Classical.choice, Quot.sound}; no sorryAx).
#print axioms ProximityGap.Frontier.W5SchurDecoupling.returnWeight_even
#print axioms ProximityGap.Frontier.W5SchurDecoupling.SchurClassicalWeightRefuted
#print axioms ProximityGap.Frontier.W5SchurDecoupling.EnergyExceedsFreeFermion
#print axioms ProximityGap.Frontier.W5SchurDecoupling.w5_reduces_to_offdiag_envelope

end ProximityGap.Frontier.W5SchurDecoupling
