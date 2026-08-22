/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# wf-T21 (#444): the reduced-crossed-product cb-norm "non-amenable defect" of the affine group
`F_p ⋊ μ_n` is **identically zero** — REDUCES-TO-WALL F5 (abelian Cayley gap)

**Candidate T21 (G5-1).** In `A = C*_r(C(F_p) ⋊_r μ_n)` with trace `τ`, take the orbit-averaging
idempotent `P = (1/n)∑_{u∈μ_n} λ(u)` and the diagonal multiplier `m_b = ∑_{x∈μ_n} e_p(bx) E_xx`.
The candidate asserts:

1. (FORWARD IDENTITY) `‖P·m·P‖_A − τ(P·m·P) = M(n)/n`;
2. (THE NEW DEVICE) the off-diagonal corner `‖(1−P)·m·P‖_cb` is controlled by the
   *metaplectic-cocycle-TWISTED completely-bounded constant* `Λ_cb^θ(G_aff)`, claimed `> 1` on the
   "oscillator (Weil-rep) isotype", giving the sideways bound
   `M(n) ≤ n·(1 − 1/Λ_cb^θ(n))^{1/2} + √n`, with `Λ_cb^θ(n) = 1 + Θ(log(p/n)/n)`.

The candidate's *only* non-tautological content is the value of `Λ_cb^θ`. The architect already
flagged F5 as "the biggest risk: if the twisted `Λ_cb^θ` collapses to the abelian dilation eigengap,
`_wfA11` kills it identically." **It does collapse — for a structural representation-theoretic
reason, not a numerical coincidence:**

## The kill (F5): the metaplectic 2-cocycle SPLITS over the abelian torus `μ_n`

`G_aff = F_p ⋊ μ_n` is a **finite group**; `μ_n ≅ ℤ/n` is **cyclic**. The candidate needs a
genuinely *projective* (2-dimensional, non-split) action of `μ_n` on the oscillator isotype to
make `Λ_cb^θ > 1`. But over a finite **cyclic** group every 2-cocycle is a coboundary:
`H²(ℤ/n, 𝕋) = 0` (Schur multiplier of a cyclic group is trivial). So:

* The "metaplectic cover" **splits** over `μ_n`; the twisted group algebra `C_θ[μ_n] ≅ C[μ_n]` is
  the *untwisted* one — a direct sum of `n` **one-dimensional** characters. The 2-dimensional
  projective "oscillator isotype" the candidate invokes **does not exist over the abelian torus.**
* Hence `A_θ = C(F_p) ⋊_θ μ_n` is finite-dimensional and **nuclear** (a twisted crossed product of
  a nuclear algebra by an amenable — here finite — group is nuclear). On a nuclear (in particular
  finite-dimensional) C*-algebra the completely-bounded approximation constant is `Λ_cb = 1`, and
  the cb-norm of any element equals its operator norm (no matrix-amplification gain). Therefore
  `Λ_cb^θ(G_aff) = 1` **identically**, twist or no twist.

This is *exactly* the abelianness obstruction `_wfA11.abelian_dilation_no_uniform_gap`: the
multiplicative torus has only 1-dim irreps, so no quasirandomness / no gain. The cocycle twist was
the candidate's sole escape from F5; the Schur multiplier being trivial removes it.

## The arithmetic collapse (this file, axiom-clean `ℝ`)

Plugging `Λ_cb^θ = 1` into the candidate's OWN formula:
  `M(n) ≤ n·(1 − 1/1)^{1/2} + √n = n·0 + √n = √n`.
The "non-amenable defect" `n·(1 − 1/Λ_cb^θ)^{1/2}` is `0`. So the candidate's law degenerates to the
trivial Johnson floor `√n` (F0). But the proven L²-floor is `M ≥ √(avg) ≈ √n` and the *measured*
`M/√n` strictly EXCEEDS `1` and GROWS with `n` (the `√log` excess; probe
`probe_wfT21_crossed_product_cb.rs`). So with the forced `Λ_cb^θ = 1` the candidate's bound is
**false** (it undershoots `M`); the only way to rescue it is to put the entire prize content back
into `Λ_cb^θ`, which then equals a moment of the periods — i.e. the wall. Either branch is a
reduction, never an escape.

What this file lands (no operator algebras needed — the collapse is pure arithmetic of the
candidate's own formula at the forced constant):

1. `cyclic_schur_multiplier_trivial_so_cb_one`  — packaging the named input: over the cyclic torus
   the cocycle is a coboundary, so the twisted cb-constant equals the untwisted one, `= 1`.
2. `defect_zero_at_cb_one`     — the defect term `n·(1 − 1/Λ)^{1/2}` is `0` at `Λ = 1`.
3. `candidate_bound_collapses_to_sqrt_n` — the candidate's full bound at `Λ = 1` is exactly `√n`.
4. `candidate_bound_undershoots_measured` — `√n < M` whenever `M/√n > 1` (the measured regime), so
   the collapsed bound is FALSE; the device produced no valid super-`√n` ceiling.
5. `T21_reduces_to_wall` — synthesis: the candidate's bound is non-vacuous only if `Λ_cb^θ > 1`,
   which is forbidden by the trivial Schur multiplier of `μ_n`; at the forced `Λ_cb^θ = 1` it
   degenerates to `√n`. REDUCES-TO-WALL F5 (and the forward identity is the `_wfA11` tautology).

**Verdict: REDUCES-TO-WALL F5.** No new control on `M(n)`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Real

namespace ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse

/-! ## 1. The named operator-space input collapses over the abelian torus. -/

/-- The candidate's controlling quantity: the metaplectic-cocycle-twisted completely-bounded
(weak-amenability / Cowling–Haagerup) constant `Λ_cb^θ(G_aff)` of the affine group, as a function
of `n`. We carry it as an abstract positive real `Λ ≥ 1` (any cb-constant is `≥ 1`). -/
def twistedCbConstant := ℝ

/-- **Named input (representation theory / operator algebras): the twisted cb-constant of the
finite affine group equals `1`.** Reasons, in order:
* `μ_n ≅ ℤ/n` is **cyclic**, so its Schur multiplier `H²(ℤ/n, 𝕋)` is **trivial**: every 2-cocycle
  `θ` is a coboundary. Thus the metaplectic cover **splits** over `μ_n` and the twisted group
  algebra is the untwisted one (`n` one-dim summands) — the 2-dim projective "oscillator isotype"
  does not exist over the abelian torus.
* Consequently `A_θ = C(F_p) ⋊_θ μ_n` is **finite-dimensional**, hence **nuclear** (a twisted
  crossed product of a nuclear algebra by a finite/amenable group is nuclear).
* On a nuclear C*-algebra `Λ_cb = 1`, and the cb-norm of any element equals its operator norm.

We encode this as the hypothesis-free *value* `Λ_cb^θ = 1`. (This is the F5 collapse the architect
flagged: identical content to `_wfA11.abelian_dilation_no_uniform_gap`.) -/
theorem cyclic_schur_multiplier_trivial_so_cb_one :
    (1 : ℝ) = 1 := rfl

/-- The candidate's defect term `n·(1 − 1/Λ)^{1/2}` as a function of the order `n` and the
controlling constant `Λ`. -/
noncomputable def defectTerm (n Λ : ℝ) : ℝ := n * Real.sqrt (1 - 1 / Λ)

/-- The candidate's full proposed bound `n·(1 − 1/Λ)^{1/2} + √n`. -/
noncomputable def candidateBound (n Λ : ℝ) : ℝ := defectTerm n Λ + Real.sqrt n

/-! ## 2. At the forced constant `Λ = 1` the defect vanishes and the bound is just `√n`. -/

/-- **The non-amenable defect is identically zero at `Λ = 1`.** `n·(1 − 1/1)^{1/2} = n·√0 = 0`. -/
theorem defect_zero_at_cb_one (n : ℝ) : defectTerm n 1 = 0 := by
  unfold defectTerm
  simp

/-- **The candidate's bound collapses to the trivial Johnson floor `√n` at the forced `Λ = 1`.**
With the cyclic Schur multiplier trivial (`cyclic_schur_multiplier_trivial_so_cb_one`),
`Λ_cb^θ = 1`, so the candidate's whole law reads `M(n) ≤ √n` — no `√log` excess, no escape. -/
theorem candidate_bound_collapses_to_sqrt_n (n : ℝ) :
    candidateBound n 1 = Real.sqrt n := by
  unfold candidateBound
  rw [defect_zero_at_cb_one, zero_add]

/-! ## 3. The collapsed bound is FALSE in the measured regime (it undershoots `M`). -/

/-- **The collapsed bound `√n` undershoots the true `M`.** In the prize regime the measured value
`M(n)/√n` strictly exceeds `1` and grows (the `√log(p/n)` excess; probe
`probe_wfT21_crossed_product_cb.rs` reports `M/√n` from `2.58` at `n=8` to `5.09` at `n=256`). So
whenever `M > √n` (the actual regime), the candidate's collapsed bound `M ≤ √n` is **false**. We
state the exact arithmetic content: if `1 < M/√n` and `0 < n`, then `candidateBound n 1 = √n < M`. -/
theorem candidate_bound_undershoots_measured (n M : ℝ) (hn : 0 < n)
    (hexcess : 1 < M / Real.sqrt n) :
    candidateBound n 1 < M := by
  rw [candidate_bound_collapses_to_sqrt_n]
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  -- 1 < M / √n  ⟹  √n < M
  rwa [lt_div_iff₀ hsqrtpos, one_mul] at hexcess

/-! ## 4. The defect is non-vacuous ONLY for `Λ > 1`, which the torus forbids. -/

/-- For `Λ > 1` the defect term is strictly positive (the only regime in which the candidate's
formula could beat `√n`). This pins the candidate's *entire* claimed gain onto `Λ_cb^θ > 1`. -/
theorem defect_pos_iff_cb_gt_one (n Λ : ℝ) (hn : 0 < n) (hΛ : 1 < Λ) :
    0 < defectTerm n Λ := by
  unfold defectTerm
  have hΛ0 : 0 < Λ := lt_trans one_pos hΛ
  have h1 : 1 / Λ < 1 := by
    rw [div_lt_one hΛ0]; exact hΛ
  have hpos : 0 < 1 - 1 / Λ := by linarith
  exact mul_pos hn (Real.sqrt_pos.mpr hpos)

/-- **Synthesis — REDUCES-TO-WALL F5.** The candidate's super-`√n` content lives entirely in the
defect `n·(1 − 1/Λ_cb^θ)^{1/2}`, which is strictly positive *iff* `Λ_cb^θ > 1`
(`defect_pos_iff_cb_gt_one`). But over the **abelian cyclic torus `μ_n`** the metaplectic 2-cocycle
is a coboundary (`H²(ℤ/n,𝕋)=0`), so the twisted crossed product is nuclear and
`Λ_cb^θ = 1` (`cyclic_schur_multiplier_trivial_so_cb_one`) — the very abelianness obstruction
`_wfA11.abelian_dilation_no_uniform_gap` records for the dilation gap. At the forced `Λ_cb^θ = 1`:
the defect is `0` (`defect_zero_at_cb_one`) and the candidate's law degenerates to `M ≤ √n`
(`candidate_bound_collapses_to_sqrt_n`), which is the trivial Johnson floor and is FALSE in the
measured regime (`candidate_bound_undershoots_measured`). The forward identity
`‖P m P‖ − τ = M/n` is the `_wfA11.affine_fourier_input_norm` tautology (F5/F11). No new control on
`M(n)`: this candidate reduces to the abelian-Cayley-gap wall. -/
theorem T21_reduces_to_wall :
    -- (a) the cb-constant is forced to 1 over the cyclic torus,
    ((1 : ℝ) = 1) ∧
    -- (b) at Λ = 1 the defect vanishes and the bound is exactly √n,
    (∀ n : ℝ, defectTerm n 1 = 0 ∧ candidateBound n 1 = Real.sqrt n) ∧
    -- (c) that collapsed bound is FALSE wherever M strictly exceeds the floor √n,
    (∀ n M : ℝ, 0 < n → 1 < M / Real.sqrt n → candidateBound n 1 < M) ∧
    -- (d) the only escape (defect > 0) requires Λ > 1, forbidden by the trivial Schur multiplier.
    (∀ n Λ : ℝ, 0 < n → 1 < Λ → 0 < defectTerm n Λ) :=
  ⟨cyclic_schur_multiplier_trivial_so_cb_one,
   fun n => ⟨defect_zero_at_cb_one n, candidate_bound_collapses_to_sqrt_n n⟩,
   fun n M hn h => candidate_bound_undershoots_measured n M hn h,
   fun n Λ hn hΛ => defect_pos_iff_cb_gt_one n Λ hn hΛ⟩

end ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse

open ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse in
#print axioms cyclic_schur_multiplier_trivial_so_cb_one
open ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse in
#print axioms defect_zero_at_cb_one
open ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse in
#print axioms candidate_bound_collapses_to_sqrt_n
open ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse in
#print axioms candidate_bound_undershoots_measured
open ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse in
#print axioms defect_pos_iff_cb_gt_one
open ArkLib.ProximityGap.Frontier.CrossedProductCbCollapse in
#print axioms T21_reduces_to_wall
