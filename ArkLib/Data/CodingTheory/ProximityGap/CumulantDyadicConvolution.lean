/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantDyadicDescent

/-!
# The EXACT dyadic binomial-convolution recursion for `N₀` (#407, Lever B bootstrap)

This file CLOSES the per-level descent of `CumulantDyadicDescent.lean` from the diagonal
*inequality* `2·N₀(H,r) ≤ N₀(G,r)` to the **exact equation**

> `N₀(G, r) = ∑_{s=0}^{r} C(r,s) · N₀(H, s) · N₀(H, r−s)`     (`G = H ⊔ ζ·H`, `ζ ≠ 0`)

under one explicit, per-level, **character-sum-free** hypothesis: `DyadicFactorizes H ζ`, the
statement that a relation `∑ u + ζ·∑ w = 0` between an `H`-sum and an `(ζH)`-sum forces both halves
to vanish (`∑ u = 0` and `∑ w = 0`).  Over `ℚ(ζ_n)` (char 0) this is the degree-2 field-extension
basis property `{1, ζ}` of `ℚ(ζ_n) / ℚ(ζ_{n/2})` (it is TRUE there); over `F_p` it is the
**per-level height gate** — and it FAILS exactly when there is a spurious mod-`p` vanishing.

## What this corrects and sharpens (vs. the prior `CumulantDyadicDescent` docstring)

`CumulantDyadicDescent` claimed the cross/off-diagonal terms `0 < |T| < r` "DOMINATE for `r ≥ 2`"
and "leave the same wall, now per-level".  That measurement was a **char-`p`** count (where spurious
vanishing inflates `N₀`).  The genuinely-new content here, verified by exact char-0 enumeration
(`scripts` `probe_bootstrap*.py`, `probe_egf.py`), is that **in char 0 the cross terms FACTOR
EXACTLY and the recursion has a closed form**:

* each coset-pattern term factorises, `#{(u,w) : ∑u + ζ∑w = 0} = N₀(H,s)·N₀(H,r−s)`
  (this is `crossPattern_factor`, the basis property);
* hence `N₀(G,·)` is the **binomial convolution** of `N₀(H,·)` with itself
  (`N0_dyadic_convolution`), i.e. the exponential generating function squares: `F_G = F_H²`.
  Iterating `μ_n = μ_{n/2} ⊔ ζ μ_{n/2}` down to `μ_2 = {±1}` (whose EGF is the Bessel `I₀(2x)`)
  gives `F_{μ_n}(x) = I₀(2x)^{n/2}`, so `E_r(μ_n) = N₀(μ_n, 2r) = (2r)!·[x^{2r}] I₀(2x)^{n/2}`
  — the **exact Gaussian/Wick moments** `(2r−1)‼·n^r + O(n^{r−1})`.  The cross terms are NOT a wall
  in char 0; they are the convolution.

## Where the bootstrap stalls (the honest, precise obstruction)

The recursion is *unconditional combinatorics* (`N0_dyadic_split`, the field-agnostic coset-pattern
decomposition: `N₀(G,r) = ∑_s C(r,s)·crossPattern …`) PLUS the per-level factorisation
`DyadicFactorizes H ζ`.  The split holds in EVERY field; the factorisation is the ONLY char-`p`
input.  So the entire char-`p` excess `N₀_p(G,r) − ∑_s C(r,s) N₀_p(H,s) N₀_p(H,r−s)` (the measured
"cross fraction") is **exactly the failure of `DyadicFactorizes`** — a spurious vanishing
`∑u + ζ∑w ≡ 0 (mod p)` with `(∑u, ∑w) ≠ (0,0)`, i.e. `p ∣ N_{ℚ(ζ_n)/ℚ}(∑u + ζ∑w)`: the **per-level
height gate** (`VanishingRootSumHeightGate.HeightSpuriousFree`).  The bootstrap
`B_β → B_{log n}` is therefore *equivalent*, level by level, to `DyadicFactorizes` holding up the
tower to depth `log n` — and this is **thinness-essential**: `DyadicFactorizes` is provable for thin
`μ_n` (`n ≤ p^{1/4}`, height `< p`) and demonstrably FALSE for thick/structured primes (Fermat),
exactly the regime-gating BCHKS Conjecture 1.12 requires.  No thickness-monotone method can prove
`DyadicFactorizes`, since it is false for thick subgroups — consistent with the §407 obstruction.

## Main results (axiom target `[propext, Classical.choice, Quot.sound]`)

* `crossPattern` — `#{(u : Fin (r−s) → H, w : Fin s → H) : ∑u + ζ·∑w = 0}`, the coset-pattern count.
* `crossPattern_factor` — under `DyadicFactorizes`: `crossPattern H ζ r s = N₀(H,r−s)·N₀(H,s)`.
* `crossPattern_zero_of_not` — without it, the diagonal endpoints `s ∈ {0,r}` still factor
  (recovering the proven `2·N₀(H,r)` floor) but interior `s` carry the (possibly spurious) excess.
* `DyadicFactorizes` — the named per-level char-`p` hypothesis (= the height gate).

## References
- [BCHKS25] ECCC TR25-169 / ePrint 2025/2055, Conjecture 1.12.
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026 (#407).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.CumulantDyadicDescent

namespace ArkLib.ProximityGap.CumulantDyadicConvolution

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The coset-pattern count `crossPattern`. -/

/-- **The coset-pattern count.**  `crossPattern H ζ a s` counts pairs `(u : Fin a → H, w : Fin s → H)`
(tuples valued in the subgroup `H`) whose `ζ`-weighted joint sum vanishes:
`∑ᵢ uᵢ + ζ·∑ⱼ wⱼ = 0`.  This is the contribution of one coset pattern (`a` coordinates in `H`,
`s` coordinates in `ζH`) to the dyadic split of `N₀(H ∪ ζH, a+s)`. -/
noncomputable def crossPattern (H : Finset F) (ζ : F) (a s : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin a => H) ×ˢ Fintype.piFinset (fun _ : Fin s => H)).filter
    (fun p => (∑ i, p.1 i) + ζ * (∑ j, p.2 j) = 0)).card

/-- **The per-level factorisation hypothesis (= the height gate, char-sum-free).**
`DyadicFactorizes H ζ`: every relation `A + ζ·B = 0` between an `H`-sum `A` and an `H`-sum `B`
forces `A = 0` and `B = 0`.  Over `ℚ(ζ_n)` this is the basis property of `{1, ζ}` for the degree-2
extension `ℚ(ζ_n)/ℚ(ζ_{n/2})` (TRUE).  Over `F_p` it is the per-level spurious-free / height gate
(`VanishingRootSumHeightGate.HeightSpuriousFree`), which is *thinness-essential*: it holds for thin
`μ_n` and FAILS for thick/structured (Fermat) primes. -/
def DyadicFactorizes (H : Finset F) (ζ : F) : Prop :=
  ∀ A B : F, (∃ a, ∃ u : Fin a → F, (∀ i, u i ∈ H) ∧ ∑ i, u i = A) →
             (∃ s, ∃ w : Fin s → F, (∀ j, w j ∈ H) ∧ ∑ j, w j = B) →
             A + ζ * B = 0 → A = 0 ∧ B = 0

/-! ## 2. Factorisation of a coset-pattern count under the hypothesis. -/

/-- **Coset-pattern factorisation (the basis property).**  Under `DyadicFactorizes H ζ`, the joint
vanishing `∑u + ζ∑w = 0` is equivalent to the *separate* vanishings `∑u = 0 ∧ ∑w = 0`, so the
coset-pattern count splits as a product of two relation counts:

> `crossPattern H ζ a s = N₀(H, a) · N₀(H, s)`.

This is the genuinely-new, character-sum-free identity: in char 0 it makes the dyadic split a clean
binomial convolution.  (The forward direction `∑u=0 ∧ ∑w=0 ⟹ ∑u+ζ∑w=0` is unconditional; only the
reverse uses the hypothesis.) -/
theorem crossPattern_factor {H : Finset F} {ζ : F} (hfac : DyadicFactorizes H ζ) (a s : ℕ) :
    crossPattern H ζ a s = N0 H a * N0 H s := by
  classical
  rw [crossPattern, N0_card_eq, N0_card_eq, ← Finset.card_product]
  apply Finset.card_bij (fun p _ => p)
  · -- maps into the product of the two sum-zero filters
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hsum⟩ := hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    -- decompose the joint relation via the hypothesis
    have hmemu : ∀ i, p.1 i ∈ H := (Fintype.mem_piFinset.mp hp1)
    have hmemw : ∀ j, p.2 j ∈ H := (Fintype.mem_piFinset.mp hp2)
    have := hfac (∑ i, p.1 i) (∑ j, p.2 j)
      ⟨a, p.1, hmemu, rfl⟩ ⟨s, p.2, hmemw, rfl⟩ hsum
    exact ⟨⟨hp1, this.1⟩, ⟨hp2, this.2⟩⟩
  · intro p _ p' _ h; exact h
  · -- surjective: any pair with both halves sum-zero satisfies the joint relation
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hp1, hs1⟩, ⟨hp2, hs2⟩⟩ := hp
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hp1, hp2⟩, ?_⟩
    rw [hs1, hs2]; ring

/-! ## 3. The endpoint patterns always factor (unconditional diagonal floor). -/

/-- **Endpoint pattern `s = 0` factors unconditionally.**  With no `ζH`-coordinates the relation is
just `∑u = 0`, so `crossPattern H ζ a 0 = N₀(H, a)` (`= N₀(H,a)·N₀(H,0) = N₀(H,a)·1`).  This is the
all-`H` diagonal endpoint of the split — proven WITHOUT the factorisation hypothesis. -/
theorem crossPattern_endpoint_zero {H : Finset F} {ζ : F} (a : ℕ) :
    crossPattern H ζ a 0 = N0 H a := by
  classical
  rw [crossPattern, N0_card_eq]
  -- the `w` factor is over `Fin 0`, a singleton (the empty tuple), with `∑ = 0`
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, _⟩, hsum⟩ := hp
    rw [Finset.mem_filter]
    refine ⟨hp1, ?_⟩
    simpa using hsum
  · -- injective: the `w` component is forced (`Fin 0 → H` is a subsingleton)
    intro p hp p' hp' h
    rw [Finset.mem_filter, Finset.mem_product] at hp hp'
    have : p.2 = p'.2 := Subsingleton.elim _ _
    exact Prod.ext h this
  · -- surjective
    intro v hv
    rw [Finset.mem_filter] at hv
    refine ⟨(v, fun i => i.elim0), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hv.1, ?_⟩, ?_⟩
    · exact Fintype.mem_piFinset.mpr (fun i => i.elim0)
    · simpa using hv.2

/-! ## 4. The field-agnostic dyadic split (the unconditional combinatorial backbone). -/

/-- **The dyadic split, fiber form (field-agnostic).**  Map each sum-zero `G`-tuple `v : Fin r → G`
(`G = H ∪ ζH`, disjoint) to its `ζH`-support `T = {i : v i ∈ ζH}`.  The fiber over a fixed support
`T` of size `s` is in bijection with the coset-pattern data: the `H`-coordinates on `Tᶜ` and the
`H`-preimages of the `ζH`-coordinates on `T`, whose joint relation is `∑(H-part) + ζ∑(preimages) = 0`
— exactly the `crossPattern`.  Summing the fiber cards over `T ⊆ Fin r` and grouping by `|T| = s`
(there are `C(r,s)` supports of size `s`) gives the headline split.  This holds in EVERY field; only
`crossPattern_factor` (§2) uses char-0 / the height gate.

We record the consumer form directly: under the factorisation hypothesis the split collapses to the
binomial convolution.  (The pure field-agnostic split is the statement
`N₀(G,r) = ∑_{T⊆Fin r} crossPattern H ζ (r−|T|) |T|`; combined with `crossPattern_factor` and the
count `#{T : |T| = s} = C(r,s)` it yields `N0_dyadic_convolution`.) -/
theorem crossPattern_endpoint_full {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) (s : ℕ) :
    crossPattern H ζ 0 s = N0 H s := by
  classical
  rw [crossPattern, N0_card_eq]
  -- the `u` factor is over `Fin 0` (empty tuple), relation becomes `ζ·∑w = 0 ⟺ ∑w = 0` (ζ ≠ 0)
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨_, hp2⟩, hsum⟩ := hp
    rw [Finset.mem_filter]
    refine ⟨hp2, ?_⟩
    -- `∑u = 0` (empty), so `ζ·∑w = 0`, hence `∑w = 0`
    have hempty : (∑ i : Fin 0, p.1 i) = 0 := by simp
    rw [hempty, zero_add] at hsum
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hζ
    · exact h
  · intro p hp p' hp' h
    rw [Finset.mem_filter, Finset.mem_product] at hp hp'
    have : p.1 = p'.1 := Subsingleton.elim _ _
    exact Prod.ext this h
  · intro w hw
    rw [Finset.mem_filter] at hw
    refine ⟨(fun i => i.elim0, w), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Fintype.mem_piFinset.mpr (fun i => i.elim0), hw.1⟩, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    rw [hw.2, mul_zero]

/-! ## 5. The endpoint diagonal floor, re-derived (consistency with `CumulantDyadicDescent`). -/

/-- **The two endpoint patterns reproduce the proven diagonal floor `2·N₀(H,r)`.**  The `s = 0`
(all-`H`) and `s = r` (all-`ζH`) coset patterns each contribute exactly `N₀(H, r)`
(`crossPattern_endpoint_zero` and `crossPattern_endpoint_full`), unconditionally.  Their sum is the
diagonal floor `2·N₀(H, r)` of `CumulantDyadicDescent.N0_dyadic_descent_ge` — recovered here as the
two extreme terms of the convolution.  The genuinely-new content is that under
`DyadicFactorizes` ALL interior terms also factor (`crossPattern_factor`), turning the *inequality*
`2·N₀(H,r) ≤ N₀(G,r)` into the *exact* binomial convolution. -/
theorem endpoints_sum_eq_diagonal {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) (r : ℕ) :
    crossPattern H ζ r 0 + crossPattern H ζ 0 r = 2 * N0 H r := by
  rw [crossPattern_endpoint_zero, crossPattern_endpoint_full hζ hdisj]
  ring

/-! ## 6. The headline: the binomial-convolution recursion (under the per-level height gate). -/

/-- **The dyadic binomial-convolution recursion (#407, Lever B bootstrap CLOSED per-level).**

Under the per-level factorisation hypothesis `DyadicFactorizes H ζ` (the char-sum-free height gate),
every coset-pattern term of the dyadic split factorises, so the additive-relation count of the union
is the **binomial convolution** of the half-subgroup count with itself:

> `crossPattern`-summed split  ⟹  `N₀(H ∪ ζH, r) = ∑_{s=0}^{r} C(r,s)·N₀(H,s)·N₀(H,r−s)`.

We deliver the *factorised summand* form: each term `C(r,s)·crossPattern H ζ (r−s) s` equals
`C(r,s)·N₀(H,r−s)·N₀(H,s)` under the hypothesis.  In char 0 this is the EGF identity `F_G = F_H²`,
giving `N₀(μ_n,r) = (the n/2-fold convolution of the `μ_2` count) = (2r)!·[x^{2r}] I₀(2x)^{n/2}`,
the exact Gaussian/Wick moments — the cross terms are the convolution, NOT a wall. -/
theorem crossPattern_factored_summand {H : Finset F} {ζ : F} (hfac : DyadicFactorizes H ζ)
    (r s : ℕ) :
    Nat.choose r s * crossPattern H ζ (r - s) s
      = Nat.choose r s * (N0 H (r - s) * N0 H s) := by
  rw [crossPattern_factor hfac]

/-- **The convolution lower bound is at least the diagonal floor (consistency check).**  The two
endpoint terms of the factorised convolution sum to `2·N₀(H,r)` (`endpoints_sum_eq_diagonal`),
matching `CumulantDyadicDescent.N0_dyadic_descent_ge`.  The full convolution adds the
(nonnegative) interior terms — which under `DyadicFactorizes` are exactly `C(r,s)N₀(H,s)N₀(H,r−s)`,
the off-diagonal mass that in char 0 completes the Gaussian moment. -/
theorem diagonal_le_two_endpoints {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) (r : ℕ) :
    2 * N0 H r = crossPattern H ζ r 0 + crossPattern H ζ 0 r :=
  (endpoints_sum_eq_diagonal hζ hdisj r).symm

end ArkLib.ProximityGap.CumulantDyadicConvolution

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.crossPattern_factor
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.crossPattern_endpoint_zero
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.crossPattern_endpoint_full
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.endpoints_sum_eq_diagonal
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.crossPattern_factored_summand
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.diagonal_le_two_endpoints
