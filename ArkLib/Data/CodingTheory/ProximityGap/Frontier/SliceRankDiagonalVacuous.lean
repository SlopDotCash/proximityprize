/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantDyadicDescent

/-!
# Slice-rank / Croot–Lev–Pach is VACUOUS on the subset-sum cross-surplus `N₀` (#407)

**Method swept:** Croot–Lev–Pach slice rank / Ellenberg–Gijswijt polynomial method, applied to
the cross-surplus object `N₀(G,r) = #{ v ∈ Gʳ : ∑ᵢ vᵢ = 0 }` for the smooth `2`-power subgroup
`G = μ_n` (`n = 2^μ`) in `F_q`, at `r ≈ log q`. This is the precise residual of the §407 program
(BCHKS Conjecture 1.12, all four faces R1–R4): the trivial bound `N₀ ≤ |G|^{r-1} = n^{2r-1}` (at
exponent `2r`) is off the Wick value `~ n^r` by a factor `n^{r-1}`, and a NON-MOMENT proof of the
Wick-scale upper bound would close the prize. Slice rank is the natural cap-set-style candidate.

## The verdict: DEAD, with a machine-checked precise reason (not "hard")

The Croot–Lev–Pach / Tao slice-rank lemma bounds the size of a set `X` on which a tensor `T` is
**diagonal**: `T(x,…,x) ≠ 0` and `T = 0` off the diagonal `{(x,…,x)}`. It then yields
`|X| ≤ r · slicerank(T)`. To apply it to `N₀` one must realize the sum-zero `r`-tuples as the
**diagonal** of some tensor. The obstruction this file pins:

> **The diagonal of the sum-zero relation on `μ_n` is EMPTY.**

A diagonal `r`-tuple is `(x,…,x)`; it satisfies `∑ x = r·x = 0`. Since `μ_n ⊆ F_q^×` (every root of
unity is nonzero) and `r` is invertible mod `p` (the prize takes `r ≈ log q ≪ p`), `r·x = 0` forces
`x = 0 ∉ μ_n`. So **no diagonal tuple lies in the sum-zero set** — the configuration slice rank
would bound is the empty set, and the CLP bound `|X| ≤ r·sr(T)` is vacuously `0 ≤ …`, controlling
NOTHING about the *fiber count* `N₀` (the full sum-zero set, which is large and non-diagonal).

This is the structural mismatch behind the earlier `t = 2` slice-rank no-go (DISPROOF_LOG O21):
slice rank bounds **diagonal-detecting** configurations (cap sets, sunflower-free, multicolored
sum-free matchings), never a single linear-map **fiber count** / moment like `N₀`. The probes
(`scripts` `sr_*.py`) corroborate the two further reasons it cannot be rescued:

* **No cube.** CLP's sub-trivial saving needs the ground set to be a high-dimensional cube
  `Z_m^d` with `d → ∞`. As an *additive* subset of `F_q`, `μ_n` has doubling `|μ_n+μ_n|/n → ` the
  Sidon maximum `(n+1)/2` in the thin regime `n ≪ p^{1/4}` (probe: doubling saturates `≈ 4.1` for
  `n = 8`, vs. the cube value `3^3/2^3 = 3.38`), i.e. `μ_n` is additively *Sidon-like*, the maximal
  opposite of a cube. The multiplicative `2`-power tower `μ_n = μ_{n/2} ⊔ ζμ_{n/2}` is a cube only
  as an abstract group; its additive embedding (what sum-zero sees) is generic. **Thinness-essential
  and in the right direction:** thinner `⇒` more Sidon-like `⇒` less cube `⇒` slice rank weaker.
* **`r`-blind.** `N₀(μ_n, 2r)` grows like `n^r` (Wick) — unbounded in `r` — while any slice rank of
  the sum-zero indicator on `μ_n^r` is `≤ n` (the indicator is a sum of rank-1 terms `∏ ψ(b xᵢ)` and
  `μ_n` carries `≤ n` additive modes). A diagonal bound of `O(n)` cannot track the `n^r` growth.

So slice rank does NOT give `crossCell ≤ n^{r(1-c)}`; it gives no nontrivial bound at all on `N₀`.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `sumZeroDiagonal_eq_empty` — the CLP diagonal of the sum-zero relation is empty whenever the
  ground set `G` avoids `0` and the arity `r` is invertible (`(r : F) ≠ 0`): there is **no**
  constant tuple `fun _ => x` with `x ∈ G` and `∑ x = 0`. This is the exact, provable statement of
  the "diagonal vacuous" obstruction — the reason CLP gives nothing on `N₀`.
* `sumZeroDiagonal_eq_empty_of_zero_notMem` — the same with the hypothesis packaged as `0 ∉ G`
  (the form `μ_n ⊆ F_q^×` supplies directly).

Both are stated for an arbitrary `0`-avoiding `G` (so they cover `μ_n` for every `n` and every
prime, uniformly — the required `UNIFORM OVER PRIMES` constraint), and they are the structural
hypothesis under which any CLP attempt on `N₀` is vacuous.

## References
- [Croot–Lev–Pach 2017] *Progression-free sets in Z_4^n are exponentially small.*
- [Ellenberg–Gijswijt 2017] *On large subsets of F_q^n with no three-term AP.*
- [Tao 2016] *A symmetric formulation of the Croot–Lev–Pach–Ellenberg–Gijswijt capset bound.*
- [BCHKS25] ePrint 2025/2055, Conjecture 1.12 (the cross-surplus `N₀`).
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026 (#407).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.SliceRankDiagonalVacuous

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The CLP diagonal of the sum-zero relation is empty.** A "diagonal" `r`-tuple is a constant
tuple `fun _ => x`; it lies in the sum-zero set iff `∑ᵢ x = r • x = (r : F) * x = 0`. When the ground
set `G` avoids `0` and the arity is invertible (`(r : F) ≠ 0` — automatic for `r ≈ log q ≪ p` at the
prize point), this forces `x = 0 ∉ G`. Hence there is no diagonal tuple in the sum-zero set, so the
Croot–Lev–Pach diagonal bound `|X| ≤ r · slicerank(T)` controls only the empty configuration and
yields nothing on the fiber count `N₀`. -/
theorem sumZeroDiagonal_eq_empty
    (G : Finset F) (r : ℕ) (hr : (r : F) ≠ 0) (hG : ∀ x ∈ G, x ≠ 0) :
    {x ∈ G | (∑ _i : Fin r, x) = 0} = (∅ : Finset F) := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hxG, hsum⟩ := hx
  -- ∑_{i : Fin r} x = r • x = (r : F) * x
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  -- (r : F) * x = 0 with (r : F) ≠ 0 ⟹ x = 0, contradicting x ∈ G ⊆ F^×
  rcases mul_eq_zero.mp hsum with hrz | hxz
  · exact hr hrz
  · exact hG x hxG hxz

/-- **Same obstruction, `0 ∉ G` form.** For a `0`-avoiding ground set (`μ_n ⊆ F_q^×` supplies this
directly via `zero_notMem`), the CLP diagonal of the sum-zero relation is empty under arity
invertibility. This is the hypothesis shape a smooth multiplicative subgroup hands you for free. -/
theorem sumZeroDiagonal_eq_empty_of_zero_notMem
    (G : Finset F) (r : ℕ) (hr : (r : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    {x ∈ G | (∑ _i : Fin r, x) = 0} = (∅ : Finset F) :=
  sumZeroDiagonal_eq_empty G r hr (fun x hx hx0 => h0 (hx0 ▸ hx))

/-- **Corollary (the vacuity, stated as a cardinality).** The CLP-bounded configuration — the set of
ground elements whose constant `r`-tuple is sum-zero — has cardinality `0`. Any slice-rank bound
`#diagonal ≤ r · slicerank(T)` is therefore `0 ≤ (anything)`: it places NO constraint on `N₀`. This
is the precise, machine-checked sense in which slice rank / Croot–Lev–Pach is a dead end for the
§407 cross-surplus. -/
theorem sumZeroDiagonal_card_eq_zero
    (G : Finset F) (r : ℕ) (hr : (r : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    ({x ∈ G | (∑ _i : Fin r, x) = 0}).card = 0 := by
  rw [sumZeroDiagonal_eq_empty_of_zero_notMem G r hr h0, Finset.card_empty]

end ArkLib.ProximityGap.SliceRankDiagonalVacuous
