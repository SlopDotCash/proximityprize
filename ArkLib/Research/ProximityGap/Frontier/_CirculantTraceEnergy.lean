/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The NCG / operator-trace NO-GO (N9) — spectral-action invariants degenerate to the moment method (#407/#444)

This is a **NEGATIVE / guardrail** brick.  It does **not** close the prize; it proves that an entire
family of exotic routes — the **noncommutative-geometry / spectral-action / Dixmier-trace** lens —
is *structurally incapable* of producing anything the elementary moment method does not already give.
It joins the ~40-lens "exotic sweep" recorded against #407/#444 (tropical, Croot–Sisask, theta/Weil,
tensor-net, restriction, pseudospectrum, Chebotarev, RMT/matrix-Bernstein, free-probability,
QUE/Iwaniec–Sarnak, ℓ-adic-Katz–Mellin, slice-rank, Talagrand/LSI, motivic/o-minimal, NCG/Connes, …),
*every one* of which reduces to the BGK moment wall.

## The object

The prize is `M(n) = max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} ψ(b·x)`, the sup-norm of an incomplete
character sum over the order-`n` (`n = 2^μ`) multiplicative subgroup `μ_n ≤ F_p^×`, in the regime
`n ~ p^{1/4}`, index `m = (p−1)/n ~ 2^128`.  Equivalently `M(n) = λ₂` of the generalized Paley graph
`Cay(F_p, μ_n)`.

## The NCG / operator-trace mechanism (and why it dies)

The `μ_n`-translation **convolution operator** `T` on functions `f : F_p → ℂ`,

> `(T f)(y) = ∑_{x ∈ μ_n} f(y + x)`,

is the adjacency-type operator of `Cay(F_p, μ_n)`.  It is **normal** and **diagonalized by the additive
characters** `χ_b(y) = ψ(b·y)`, with eigenvalues exactly the Gauss periods `η_b`:

* `circulant_eigenvalue_eq_eta` : `T χ_b = η_b · χ_b`  (the additive characters are an eigenbasis).

Consequently `|T|^{2r}` has eigenvalues `‖η_b‖^{2r}`, and its **normalized trace** (the Dixmier /
spectral-action invariant the NCG lens would compute) is

* `trace_abs_pow_eq_energy` : `(1/p)·∑_b ‖η_b‖^{2r} = E_r(μ_n)`,

the `r`-fold **additive energy** — *exactly* the quantity the moment method already controls
(`subgroup_gaussSum_moment` : `∑_b ‖η_b‖^{2r} = p·E_r`).  So **every** spectral-action / Dixmier-trace
/ heat-kernel-`ζ`-function invariant of `T` is a function of the trace moments `(1/p)∑‖η_b‖^{2r}`,
i.e. of the energies `E_r` — the very sequence whose `r ≈ log p` saddle **is** the BGK wall.  The NCG
route therefore **consumes** the moment hierarchy rather than producing cancellation outside it; it
cannot beat BGK because trace ⟹ RMS ⟹ moment method.

This matches the three-property necessary condition for any closer (#407): a winning argument must
exhibit cancellation **outside the moment hierarchy**, and the trace functional is *inside* it (it is
literally the sum of the `2r`-th moments).  The operator-norm reading `‖T‖ = M(n)` (the spectral
radius over `b ≠ 0`) only restates the prize, supplying no second endomorphism to amplify against —
the "hypothesis-circularity" archetype of the sweep.

## What is proven here (axiom-clean)

* `convOp_apply`, `chi_apply` : unfolding lemmas for `T` and the character eigenvector.
* `circulant_eigenvalue_eq_eta` : the eigen-equation `(T χ_b) y = η_b · χ_b y`, pointwise.
* `convOp_smul_eq` : the operator form `T (chi b) = η_b • chi b`.
* `trace_abs_pow_eq_energy` : `(1/p)·∑_b ‖η_b‖^{2r} = E_r(μ_n)` (normalized trace of `|T|^{2r}` =
  additive energy), via the in-tree `subgroup_gaussSum_moment`.  `r = 2, 3` corollaries
  (`trace_abs_sq_eq_secondEnergy`, …) record the first invariants explicitly.

**Honesty.** This is a structural no-go, NOT a closure: the core `M(μ_n) ≤ C·√(n·log(p/n))` stays
OPEN (it is the char-`p` energy saddle / BGK wall).  This file proves only that the NCG/trace lens
re-expresses that same open quantity, so it cannot be the route that closes it.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Issue #444 (the exotic-lens sweep ledger); `ConstantIndexGaussBarrier.lean`,
  `LargeSieveParsevalCollapse.lean` (sibling guardrail bricks).
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ProximityGap.Frontier.CirculantTraceEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive character `χ_b : F → ℂ`, `χ_b(y) = ψ(b·y)`.  These are the eigenvectors of the
`μ_n`-translation convolution operator. -/
noncomputable def chi (ψ : AddChar F ℂ) (b : F) : F → ℂ := fun y => ψ (b * y)

@[simp] theorem chi_apply (ψ : AddChar F ℂ) (b y : F) : chi ψ b y = ψ (b * y) := rfl

/-- The `G`-translation **convolution operator** `T` on functions `F → ℂ`:
`(T f)(y) = ∑_{x ∈ G} f(y + x)`.  For `G = μ_n` this is the adjacency operator of the generalized
Paley graph `Cay(F, μ_n)`. -/
noncomputable def convOp (G : Finset F) (f : F → ℂ) : F → ℂ := fun y => ∑ x ∈ G, f (y + x)

@[simp] theorem convOp_apply (G : Finset F) (f : F → ℂ) (y : F) :
    convOp G f y = ∑ x ∈ G, f (y + x) := rfl

/-- **The circulant eigen-equation (pointwise): `(T χ_b)(y) = η_b · χ_b(y)`.**

The additive characters diagonalize the convolution operator `T`, with eigenvalue the subgroup Gauss
period `η_b = ∑_{x∈G} ψ(b·x)`.  Proof: `χ_b(y+x) = ψ(b(y+x)) = ψ(by)·ψ(bx) = χ_b(y)·ψ(bx)`, so
summing the `x`-shift factors out `χ_b(y)` and leaves `∑_{x∈G} ψ(bx) = η_b`. -/
theorem circulant_eigenvalue_eq_eta (ψ : AddChar F ℂ) (G : Finset F) (b y : F) :
    convOp G (chi ψ b) y = eta ψ G b * chi ψ b y := by
  classical
  simp only [convOp_apply, chi_apply, eta]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_add, AddChar.map_add_eq_mul]
  ring

/-- **The operator form of the eigen-equation: `T (χ_b) = η_b • χ_b`.**
`T` is normal and diagonalized by the additive-character basis; this is `circulant_eigenvalue_eq_eta`
as an equality of functions (scalar `•` on `F → ℂ`). -/
theorem convOp_smul_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    convOp G (chi ψ b) = eta ψ G b • chi ψ b := by
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  exact circulant_eigenvalue_eq_eta ψ G b y

/-- **The normalized trace of `|T|^{2r}` is the additive energy: `(1/p)·∑_b ‖η_b‖^{2r} = E_r(μ_n)`.**

Since `T` is diagonalized by the `p` additive characters with eigenvalues `η_b`, the operator
`|T|^{2r}` has eigenvalues `‖η_b‖^{2r}`, so its trace is `∑_b ‖η_b‖^{2r}`.  Normalizing by the
dimension `p = |F|` gives exactly the `r`-fold additive energy `E_r(μ_n)` — the moment-method
quantity.  Every Dixmier-trace / spectral-action invariant of `T` is a function of these normalized
trace moments, hence of the energies `E_r`, whose `r ≈ log p` saddle is the BGK wall.

Uses the in-tree `subgroup_gaussSum_moment` (`∑_b ‖η_b‖^{2r} = p·E_r`). -/
theorem trace_abs_pow_eq_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) / (Fintype.card F : ℝ) = rEnergy G r := by
  rw [subgroup_gaussSum_moment hψ G r, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast hq.ne'), mul_one]

/-- **`r = 1`: the normalized trace of `|T|²` is the second additive energy** (`E₁ = |G|`,
the Parseval/second-moment invariant). -/
theorem trace_abs_sq_eq_firstEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2) / (Fintype.card F : ℝ) = rEnergy G 1 := by
  have := trace_abs_pow_eq_energy hψ G 1 hq
  simpa using this

/-- **`r = 2`: the normalized trace of `|T|⁴` is the (4th-moment) additive energy `E₂(μ_n)`.** -/
theorem trace_abs_pow_four_eq_secondEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 4) / (Fintype.card F : ℝ) = rEnergy G 2 := by
  have := trace_abs_pow_eq_energy hψ G 2 hq
  simpa using this

/-- **`r = 3`: the normalized trace of `|T|⁶` is the (6th-moment) additive energy `E₃(μ_n)`.** -/
theorem trace_abs_pow_six_eq_thirdEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 6) / (Fintype.card F : ℝ) = rEnergy G 3 := by
  have := trace_abs_pow_eq_energy hψ G 3 hq
  simpa using this

/-- **The trace ⟹ moment-method degeneration, restated.**  The full (un-normalized) trace of
`|T|^{2r}` is `p · E_r(μ_n)` — i.e. the entire NCG/Dixmier-trace functional of `T` equals `p` times
the additive energy, the quantity whose `r ≈ log p` saddle is the BGK wall.  No spectral-action
invariant escapes the moment hierarchy. -/
theorem trace_abs_pow_eq_fieldSize_mul_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) :
    ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r :=
  subgroup_gaussSum_moment hψ G r

end ProximityGap.Frontier.CirculantTraceEnergy

/-! ## Axiom audit (must be `[propext, Classical.choice, Quot.sound]` only) -/
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.circulant_eigenvalue_eq_eta
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.convOp_smul_eq
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.trace_abs_pow_eq_energy
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.trace_abs_sq_eq_firstEnergy
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.trace_abs_pow_four_eq_secondEnergy
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.trace_abs_pow_six_eq_thirdEnergy
#print axioms ProximityGap.Frontier.CirculantTraceEnergy.trace_abs_pow_eq_fieldSize_mul_energy
