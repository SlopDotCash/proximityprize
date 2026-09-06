/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueDegeneracySupport
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueRankDeficient

/-!
# Assault V2 — Lever `CONJ41_C_height`: the Open-Set-Rank degeneracy escape + realizability height
# (Chai–Fan 2026/858 §7; dossier §6.4)

## What this file banks

The prize-favorable reading of Conjecture 41 was: "there is a polynomial `p₀` such that for every
prime `p > p₀` the `(w+1)`-clique normal matrix `A = [N | γN]` has full rank `D + c`, hence
`M_true < k` (no above-Johnson list element)". Two facts already proven in-tree
(`Round20CliqueKernel`, `Round23CliqueDegeneracy`) destroy that reading:

* **(K) The clique pencil is in the kernel over EVERY field.** `clique_kernel_mem` exhibits, for an
  *arbitrary* weight `b : F → F` and twist `γ`, an explicit kernel vector of `A`. So `A` is
  rank-deficient unconditionally — there is **no special prime `p₀`** restoring full rank.
* **(R) The deficiency is `≥ w+1` over every field, with the SAME floor `W.card`.**
  `cliqueKernelSpace_finrank_ge`.

This file welds those into **one** axiom-clean headline that permanently banks the
"identically-zero rank deficiency, not a mod-p coincidence" verdict (`conj41_no_good_prime`), and
then **REFUTES the degeneracy escape clause**.

## The degeneracy escape clause, and why it is FALSE

The only surviving prize-favorable reading was: *maybe every persistent rank-deficient syndrome is
"degenerate" — a false positive supported on the `(w+1)`-set with **not all** error values
nonzero (some `b(α) = 0`).* If true, a genuine full-weight error could never sit in the kernel, and
the above-Johnson list element would be a phantom.

This is **false** for the clique, over every field. Take `b = (fun _ => 1)` — a full-weight
(all-coordinates-nonzero) weight vector. By `clique_kernel_mem` its pencil `s₂(b)` lies in the
kernel; by `pairing_kernel_pencil_ne_zero_iff` every coordinate weight is recoverable and nonzero,
so the kernel member is a **genuine weight-`(w+1)` error** on `W`. Hence *not* every kernel member
is degenerate — there is an all-nonzero one over any field (`clique_full_weight_kernel_member`,
`degeneracy_escape_clause_false`).

## Consequence for the prize

After both the no-`p₀` weld and the degeneracy refutation, Conjecture 41 cannot supply the prize
upper bound through "rank over `ℚ`" + "good prime existence". The ONLY remaining lever is **(ii)**:
bound the log-height of the all-nonzero-realizability resultant by `poly(n)`. The PTE witness
`E1 = {0,1,5,8,12,21}` makes the height exponential explicit (computed in the docstring below): the
clique relation coefficients are the Lagrange weights `c(α) = 1/N'(α)`, with denominators whose lcm
is `2^6·3^3·5·7·11·13 = 8 648 640` already at `w+1 = 6` nodes — the **E2W4 residual replicated at
codim `c ≥ 3`, exponential, not discharged**. This file does NOT close that height question; it
banks the structural verdict and refutes the degeneracy escape, which is the bankable content.

## Exact PTE numerics (probe, not proof — `python3` exact rationals)

`W = {0,1,5,8,12,21}` (`w+1 = 6` nodes). The clique row dependency is the divided-difference
power-sum identity: with `c(α) = 1/N'(α)`, `N(X) = ∏_{β∈W}(X−β)`,

```
Σ_{α∈W} c(α)·α^k = 0  for k = 0,1,2,3,4 (= 0..w−1),   = 1 for k = w = 5.
```

(verified exactly: weights `[-1/10080, 1/6160, -1/6720, 1/8736, -1/33264, 1/786240]`, all NONZERO ⇒
the canonical clique relation is full-weight ⇒ degeneracy escape is false; lcm of denominators
`= 8 648 640 = 2^6·3^3·5·7·11·13`, the integer-height witness). The relation holds over every field
of characteristic not dividing a pairwise difference `{1,3,4,5,7,8,9,11,12,13,16,20,21}` (primes
`2,3,5,7,11,13`) — i.e. over every prime where `W` stays `6` distinct residues.

NON-MOMENT structural (rides the in-tree clique duality; no Wick/energy/char-sum). Honest scope:
this banks the "no `p₀`" + "degeneracy escape false" verdicts; the realizability **height** bound
remains the OPEN §6.4 residual (REDUCES_TO the E2W4 exponential-height wall).
-/

set_option autoImplicit false

open Polynomial Finset

namespace ProximityGap.AssaultV2Conj41Height

open Round20CliqueKernel Round23CliqueDegeneracy

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The "no good prime" weld — the rank deficiency is identically zero over every field -/

/-- **HEADLINE (no `p₀`).** Over *every* field `F` (so in particular `ℚ` and every `𝔽ₚ`), and for
*every* twist `γ`, the `(w+1)`-clique kernel space `cliqueKernelSpace D W γ` has dimension at least
`W.card = w+1`. There is therefore **no special prime `p₀`** at which the clique configuration
becomes full-rank: the rank deficiency is structural (identically zero), not an arithmetic
mod-`p` coincidence. This permanently kills the "poly `p₀` ⟹ prize" reading of Conjecture 41. -/
theorem conj41_no_good_prime (W : Finset F) (γ : F → F) {D : ℕ} (hD : W.card - 1 < D) :
    W.card ≤ Module.finrank F (cliqueKernelSpace D W γ) :=
  cliqueKernelSpace_finrank_ge W γ hD

/-! ## 2. The degeneracy escape clause is FALSE: a full-weight (all-nonzero) clique error sits in
       the kernel over every field. -/

/-- The all-ones weight vector — a *full-weight* error: every coordinate is `1 ≠ 0`. -/
def fullWeight (F : Type*) [Field F] : F → F := fun _ => 1

/-- **The all-ones pencil is a genuine kernel member.** For the twisted clique condition with weight
`b = 1`, every kernel equation `⟨Λ_{E_α}X^r, s₁⟩ + γ(α)·⟨Λ_{E_α}X^r, s₂⟩ = 0` holds at each vertex
`α ∈ W` and each admissible `r`. (Direct specialization of `clique_kernel_mem` at `b = fun _ => 1`.) -/
theorem clique_full_weight_kernel_member (W : Finset F) (γ : F → F) {α : F} (hα : α ∈ W)
    {r D : ℕ} (hD : W.card - 1 + r < D) :
    pairing D (normalPoly W α r)
        (fun j => -∑ β ∈ W, γ β * fullWeight F β * evalSyndrome D β j)
      + γ α * pairing D (normalPoly W α r)
          (fun j => ∑ β ∈ W, fullWeight F β * evalSyndrome D β j) = 0 :=
  clique_kernel_mem W γ (fullWeight F) hα hD

/-- **The full-weight error is genuinely full-weight: every coordinate weight is recoverable and
nonzero.** Pairing the all-ones kernel pencil `s₂(1)` against each locator `Λ_{E_α}` reads off a
NONZERO value, so the kernel member is a *genuine* weight-`(w+1)` error on `W`, not a degenerate
syndrome with a vanishing error value. -/
theorem fullWeight_pencil_pairing_ne_zero (W : Finset F) {α : F} (hα : α ∈ W) {D : ℕ}
    (hD : W.card - 1 < D) :
    pairing D (normalPoly W α 0) (kernelPencil W (fullWeight F) D) ≠ 0 := by
  rw [pairing_kernel_pencil_ne_zero_iff hα hD]
  -- `fullWeight F α = 1 ≠ 0`
  simp [fullWeight]

/-- **HEADLINE (degeneracy escape REFUTED).** It is *false* that every persistent rank-deficient
clique syndrome is degenerate (= has a vanishing error value at some vertex). Witness: the all-ones
weight `b = 1`. Its pencil `s₂(1)` lies in the kernel (`clique_full_weight_kernel_member`), and at
*every* vertex `α ∈ W` the recoverable error value is nonzero (`fullWeight_pencil_pairing_ne_zero`).
So there is an all-nonzero (full-weight `w+1`) kernel member over every field — the degeneracy
escape clause does not hold, and the prize cannot be banked through it. -/
theorem degeneracy_escape_clause_false (W : Finset F) {D : ℕ} (hD : W.card - 1 < D) :
    ∀ α ∈ W, pairing D (normalPoly W α 0) (kernelPencil W (fullWeight F) D) ≠ 0 := by
  intro α hα
  exact fullWeight_pencil_pairing_ne_zero W hα hD

/-! ## 3. The PTE realizability-height witness `E1 = {0,1,5,8,12,21}` (the remaining open lever).

The two facts above retire readings (rank-over-ℚ + good prime) and (degeneracy escape). The ONLY
surviving lever is the **all-nonzero realizability height** (dossier §6.4(ii)): bound
`log-height(Res)` of the resultant whose vanishing realizes the full-weight clique error as a
genuine RS codeword by `poly(n)`. The clique relation coefficients `c(α) = 1/N'(α)` make this
exponential already at `w+1 = 6`: their common denominator is

  `lcm |N'(α)| = 8 648 640 = 2^6 · 3^3 · 5 · 7 · 11 · 13`.

We record the witness node set and its size as a Lean datum so the height target is anchored
in-tree. (The exponential-height claim itself is the OPEN residual; we do NOT assert a bound.) -/

/-- The PTE realizability-height witness node set `E1 = {0,1,5,8,12,21}` over `ℚ` — `w+1 = 6`
distinct nodes. The clique relation among its locators has full-weight (all-nonzero) integer-Lagrange
coefficients with denominator `8 648 640`; bounding the realizability resultant height by `poly(n)`
is the remaining open §6.4(ii) lever (REDUCES to the E2W4 exponential-height wall). -/
def pteWitnessE1 : Finset ℚ := {0, 1, 5, 8, 12, 21}

/-- The PTE witness has the expected `w+1 = 6` distinct nodes. -/
theorem pteWitnessE1_card : pteWitnessE1.card = 6 := by decide

end ProximityGap.AssaultV2Conj41Height

#print axioms ProximityGap.AssaultV2Conj41Height.conj41_no_good_prime
#print axioms ProximityGap.AssaultV2Conj41Height.clique_full_weight_kernel_member
#print axioms ProximityGap.AssaultV2Conj41Height.fullWeight_pencil_pairing_ne_zero
#print axioms ProximityGap.AssaultV2Conj41Height.degeneracy_escape_clause_false
#print axioms ProximityGap.AssaultV2Conj41Height.pteWitnessE1_card
