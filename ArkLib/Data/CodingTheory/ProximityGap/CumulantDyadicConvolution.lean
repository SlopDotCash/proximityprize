/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantDyadicDescent

/-!
# Factorised summands of the dyadic binomial-convolution recursion for `N₀` (#407, Lever B)

The target of this file is the **exact equation**

> `N₀(G, r) = ∑_{s=0}^{r} C(r,s) · N₀(H, s) · N₀(H, r−s)`     (`G = H ⊔ ζ·H`, `ζ ≠ 0`)

sharpening the diagonal *inequality* `2·N₀(H,r) ≤ N₀(G,r)` of `CumulantDyadicDescent.lean`.
**What is actually proved here is less:** the factorisation of each coset-pattern summand
(`crossPattern_factor`, `crossPattern_factored_summand`) under a factorisation hypothesis, and the
unconditional endpoint identities (`crossPattern_endpoint_zero`, `crossPattern_endpoint_full`,
`endpoints_sum_eq_diagonal`).  The tuple-pattern split in the form
`N₀(G,r) = ∑_{T⊆Fin r} crossPattern H ζ (r−|T|) |T|` and the resulting full convolution theorem are
**not** formalized in this file (there is no `N0_dyadic_split` / `N0_dyadic_convolution`).  A
partition into pattern cells, `N₀(G,r) = ∑_T crossCell H K r T`, is proved separately in
`CumulantDyadicSplitExact.N0_dyadic_split_exact`, but the identification of those cells with
`crossPattern` is not proved.

The factorisation hypothesis comes in two forms:

* `DyadicFactorizes H ζ` — a relation `A + ζ·B = 0` between an `H`-sum `A` and an `H`-sum `B` of
  **arbitrary length** (repetitions allowed) forces `A = B = 0`.  Over `ℚ(ζ_n)` (char 0) this is
  the degree-2 basis property `{1, ζ}` of `ℚ(ζ_n) / ℚ(ζ_{n/2})`.  **Over a prime field it is
  false** as soon as `H` contains a nonzero element `h`, for every `ζ`: repeated copies of `h`
  generate all of `F_p`, so `A = −ζh` and `B = h ≠ 0` is a relation
  (`not_dyadicFactorizes_zmod`).  This includes thin dyadic examples: `p = 257`, `H = μ₂ = {±1}`,
  `ζ = 16` of order `4`, `4⁴ = 256 < 257` (`not_dyadicFactorizes_thin_example`).  The file's
  ambient `[Fintype F]` scope cannot instantiate the char-0 statement either.
* `DyadicFactorizesUpTo H ζ L` — the same implication restricted to relations of **total length**
  `≤ L`.  This bounded form is the meaningful finite-field height-gate input: a mod-`p` relation of
  small total length lifts to a genuine characteristic-zero relation when the height is `< p`.
  `crossPattern_factor_of_upTo` gives the summand factorisation for `a + s ≤ L`.  No in-tree
  theorem establishes `DyadicFactorizesUpTo` for thin subgroups; it remains an explicit
  hypothesis.

## What this corrects and sharpens (vs. the prior `CumulantDyadicDescent` docstring)

`CumulantDyadicDescent` claimed the cross/off-diagonal terms `0 < |T| < r` "DOMINATE for `r ≥ 2`"
and "leave the same wall, now per-level".  That measurement was a **char-`p`** count (where spurious
vanishing inflates `N₀`).  The observation motivating this file, from exact char-0 enumeration
(`scripts` `probe_bootstrap*.py`, `probe_egf.py`; probe evidence, not a Lean theorem), is that
**in char 0 the cross terms factor and the recursion has a closed form**:

* each coset-pattern term factorises, `#{(u,w) : ∑u + ζ∑w = 0} = N₀(H,s)·N₀(H,r−s)`
  (this is the content of `crossPattern_factor`, the basis property);
* granted the (unformalized) split, `N₀(G,·)` is then the **binomial convolution** of `N₀(H,·)`
  with itself, i.e. the exponential generating function squares: `F_G = F_H²`.
  Iterating `μ_n = μ_{n/2} ⊔ ζ μ_{n/2}` down to `μ_2 = {±1}` (whose EGF is the Bessel `I₀(2x)`)
  gives `F_{μ_n}(x) = I₀(2x)^{n/2}`, so `E_r(μ_n) = N₀(μ_n, 2r) = (2r)!·[x^{2r}] I₀(2x)^{n/2}`
  — the characteristic-zero moments, `(2r−1)‼·n^r` plus lower-order corrections (e.g.
  `E₂ = 3n² − 3n`).  This char-0 computation is commentary; it is not a theorem of this file.

## Where the bootstrap stalls (the precise obstruction)

The intended recursion is combinatorics (the field-agnostic coset-pattern decomposition
`N₀(G,r) = ∑_s C(r,s)·crossPattern …`, not formalized here) PLUS a per-level factorisation.  The
char-`p` excess `N₀_p(G,r) − ∑_s C(r,s) N₀_p(H,s) N₀_p(H,r−s)` (the measured "cross fraction")
comes from spurious vanishings `∑u + ζ∑w ≡ 0 (mod p)` with `(∑u, ∑w) ≠ (0,0)` of the relevant
**bounded** length, i.e. `p ∣ N_{ℚ(ζ_n)/ℚ}(∑u + ζ∑w)`: the per-level height gate
(`VanishingRootSumHeightGate.HeightSpuriousFree`).  Only a bounded-length gate
(`DyadicFactorizesUpTo`, length `≤ r` at order `r`) can hold over a finite field; the unbounded
`DyadicFactorizes` fails in every prime field (see above), thin or thick.  A bounded gate is
plausible for thin `μ_n` (height `< p`) and fails for thick/structured primes (Fermat), but no
in-tree theorem proves it for thin subgroups, and the full bootstrap `B_β → B_{log n}` is not
proved here.

## Main results (axiom target `[propext, Classical.choice, Quot.sound]`)

* `crossPattern` — `#{(u : Fin a → H, w : Fin s → H) : ∑u + ζ·∑w = 0}`, the coset-pattern count.
* `crossPattern_factor` — under `DyadicFactorizes`: `crossPattern H ζ a s = N₀(H,a)·N₀(H,s)`
  (vacuous over prime fields, since the hypothesis is false there).
* `crossPattern_factor_of_upTo` — the same for `a + s ≤ L` under the bounded
  `DyadicFactorizesUpTo H ζ L`.
* `crossPattern_endpoint_zero` / `crossPattern_endpoint_full` / `endpoints_sum_eq_diagonal` — the
  diagonal endpoints `s ∈ {0,r}` factor unconditionally, recovering the `2·N₀(H,r)` floor.
* `not_dyadicFactorizes_zmod` / `not_dyadicFactorizes_thin_example` — refutations of the unbounded
  predicate over prime fields, including a thin dyadic instance.

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

/-- **The unbounded per-level factorisation hypothesis.**
`DyadicFactorizes H ζ`: every relation `A + ζ·B = 0` between an `H`-sum `A` and an `H`-sum `B`,
each of **arbitrary length with repetitions**, forces `A = 0` and `B = 0`.  Over `ℚ(ζ_n)` the
analogous statement is the basis property of `{1, ζ}` for `ℚ(ζ_n)/ℚ(ζ_{n/2})`, but this file's
`[Fintype F]` scope cannot express that.  **Over a prime field it is false** whenever `H` has a
nonzero element (`not_dyadicFactorizes_zmod`), including thin dyadic subgroups
(`not_dyadicFactorizes_thin_example`).  The meaningful finite-field height gate is the bounded
`DyadicFactorizesUpTo`. -/
def DyadicFactorizes (H : Finset F) (ζ : F) : Prop :=
  ∀ A B : F, (∃ a, ∃ u : Fin a → F, (∀ i, u i ∈ H) ∧ ∑ i, u i = A) →
             (∃ s, ∃ w : Fin s → F, (∀ j, w j ∈ H) ∧ ∑ j, w j = B) →
             A + ζ * B = 0 → A = 0 ∧ B = 0

/-- **The bounded per-level factorisation hypothesis (the finite-field height gate).**
`DyadicFactorizesUpTo H ζ L`: every relation `∑ u + ζ·∑ w = 0` with `u : Fin a → H`,
`w : Fin s → H` and total length `a + s ≤ L` forces `∑ u = 0` and `∑ w = 0`.  Bounding the length
is essential: without it the predicate fails in every prime field (`not_dyadicFactorizes_zmod`).
It is an explicit hypothesis; no in-tree theorem proves it for thin subgroups. -/
def DyadicFactorizesUpTo (H : Finset F) (ζ : F) (L : ℕ) : Prop :=
  ∀ a s : ℕ, a + s ≤ L → ∀ u : Fin a → F, ∀ w : Fin s → F,
    (∀ i, u i ∈ H) → (∀ j, w j ∈ H) →
    (∑ i, u i) + ζ * (∑ j, w j) = 0 → (∑ i, u i) = 0 ∧ (∑ j, w j) = 0

/-- The unbounded predicate implies every bounded one. -/
theorem DyadicFactorizes.upTo {H : Finset F} {ζ : F} (hfac : DyadicFactorizes H ζ) (L : ℕ) :
    DyadicFactorizesUpTo H ζ L :=
  fun a s _ u w hu hw hsum => hfac _ _ ⟨a, u, hu, rfl⟩ ⟨s, w, hw, rfl⟩ hsum

/-! ## 2. Factorisation of a coset-pattern count under the hypothesis. -/

/-- **Coset-pattern factorisation (the basis property).**  Under `DyadicFactorizes H ζ`, the joint
vanishing `∑u + ζ∑w = 0` is equivalent to the *separate* vanishings `∑u = 0 ∧ ∑w = 0`, so the
coset-pattern count splits as a product of two relation counts:

> `crossPattern H ζ a s = N₀(H, a) · N₀(H, s)`.

(The forward direction `∑u=0 ∧ ∑w=0 ⟹ ∑u+ζ∑w=0` is unconditional; only the reverse uses the
hypothesis.)  Over a prime field the hypothesis `DyadicFactorizes` is false whenever `H` has a
nonzero element (`not_dyadicFactorizes_zmod`), so this form is vacuous there; use
`crossPattern_factor_of_upTo` with the bounded gate instead. -/
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

/-- **Coset-pattern factorisation under the bounded gate.**  If `DyadicFactorizesUpTo H ζ L` and
`a + s ≤ L`, then `crossPattern H ζ a s = N₀(H, a) · N₀(H, s)`.  This is the finite-field-meaningful
form of `crossPattern_factor`: only relations of total length `a + s` are used. -/
theorem crossPattern_factor_of_upTo {H : Finset F} {ζ : F} {L : ℕ}
    (hfac : DyadicFactorizesUpTo H ζ L) {a s : ℕ} (has : a + s ≤ L) :
    crossPattern H ζ a s = N0 H a * N0 H s := by
  classical
  rw [crossPattern, N0_card_eq, N0_card_eq, ← Finset.card_product]
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hsum⟩ := hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    have := hfac a s has p.1 p.2 (Fintype.mem_piFinset.mp hp1) (Fintype.mem_piFinset.mp hp2) hsum
    exact ⟨⟨hp1, this.1⟩, ⟨hp2, this.2⟩⟩
  · intro p _ p' _ h; exact h
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hp1, hs1⟩, ⟨hp2, hs2⟩⟩ := hp
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hp1, hp2⟩, ?_⟩
    rw [hs1, hs2]; ring

/-! ## 2b. The unbounded predicate is false over prime fields. -/

/-- **`DyadicFactorizes` fails in every prime field.**  If `H ⊆ ZMod p` contains a nonzero `h`,
then for every `ζ` the unbounded predicate fails: `(-ζ).val` copies of `h` sum to `A = -ζ·h`, one
copy sums to `B = h`, and `A + ζ·B = 0` while `B ≠ 0`.  Repetitions of unbounded length generate the
whole field, so the unbounded predicate cannot serve as a finite-field height gate. -/
theorem not_dyadicFactorizes_zmod {p : ℕ} [Fact p.Prime] {H : Finset (ZMod p)} {h : ZMod p}
    (hH : h ∈ H) (hh : h ≠ 0) (ζ : ZMod p) : ¬ DyadicFactorizes H ζ := by
  intro hfac
  have hA : ∃ a, ∃ u : Fin a → ZMod p, (∀ i, u i ∈ H) ∧ ∑ i, u i = -ζ * h := by
    refine ⟨(-ζ).val, fun _ => h, fun _ => hH, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ZMod.natCast_zmod_val]
  have hB : ∃ s, ∃ w : Fin s → ZMod p, (∀ j, w j ∈ H) ∧ ∑ j, w j = h :=
    ⟨1, fun _ => h, fun _ => hH, by simp⟩
  exact hh (hfac _ _ hA hB (by ring)).2

section ThinExample

local instance fact_prime_257 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- **A thin dyadic refutation of the unbounded predicate.**  In `F₂₅₇`, `ζ = 16` is a primitive
`4`-th root of unity, `H = {1, -1} = μ₂`, and the thinness condition `4⁴ = 256 < 257` holds, yet
`DyadicFactorizes H 16` is false (by `not_dyadicFactorizes_zmod`; concretely `241` copies of `1`
and one copy of `1` give `241 + 16·1 = 257 = 0`). -/
theorem not_dyadicFactorizes_thin_example :
    IsPrimitiveRoot (16 : ZMod 257) 4 ∧ (4 : ℕ) ^ 4 < 257 ∧
      ¬ DyadicFactorizes ({1, -1} : Finset (ZMod 257)) 16 := by
  refine ⟨?_, by norm_num, not_dyadicFactorizes_zmod (h := 1) (by simp) one_ne_zero 16⟩
  refine IsPrimitiveRoot.mk_of_lt _ (by decide : 0 < 4) (by decide) ?_
  intro l hl hlt
  interval_cases l <;> decide

end ThinExample

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

/-- **The all-`ζH` endpoint pattern factors.**  `crossPattern H ζ 0 s = N₀(H, s)` for `ζ ≠ 0`.

Context (the intended split, **not formalized here**).  Map each sum-zero `G`-tuple `v : Fin r → G`
(`G = H ∪ ζH`, disjoint) to its `ζH`-support `T = {i : v i ∈ ζH}`.  The fiber over a fixed support
`T` of size `s` is in bijection with the coset-pattern data: the `H`-coordinates on `Tᶜ` and the
`H`-preimages of the `ζH`-coordinates on `T`, whose joint relation is `∑(H-part) + ζ∑(preimages) = 0`
— exactly the `crossPattern`.  Summing the fiber cards over `T ⊆ Fin r` and grouping by `|T| = s`
(there are `C(r,s)` supports of size `s`) would give the split
`N₀(G,r) = ∑_{T⊆Fin r} crossPattern H ζ (r−|T|) |T|`, which combined with
`crossPattern_factor_of_upTo` (at `L = r`) and `#{T : |T| = s} = C(r,s)` would yield the
convolution.  Neither the split nor the convolution theorem is proved in this file; only this
endpoint identity is. -/
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
two extreme terms of the convolution.  Under a factorisation gate the interior terms also factor
(`crossPattern_factor_of_upTo`); turning the *inequality* `2·N₀(H,r) ≤ N₀(G,r)` into the exact
binomial convolution would additionally need the unformalized tuple-pattern split. -/
theorem endpoints_sum_eq_diagonal {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) (r : ℕ) :
    crossPattern H ζ r 0 + crossPattern H ζ 0 r = 2 * N0 H r := by
  rw [crossPattern_endpoint_zero, crossPattern_endpoint_full hζ hdisj]
  ring

/-! ## 6. The headline: the binomial-convolution recursion (under the per-level height gate). -/

/-- **Factorised summand of the dyadic convolution (not the full recursion).**

Under `DyadicFactorizes H ζ`, each term `C(r,s)·crossPattern H ζ (r−s) s` equals
`C(r,s)·N₀(H,r−s)·N₀(H,s)`.  This is only the summand identity: the split
`N₀(H ∪ ζH, r) = ∑_s C(r,s)·crossPattern H ζ (r−s) s` is not proved here, so the full recursion
`N₀(H ∪ ζH, r) = ∑_{s=0}^{r} C(r,s)·N₀(H,s)·N₀(H,r−s)` is not a theorem of this file.  Moreover the
unbounded hypothesis is false over prime fields (`not_dyadicFactorizes_zmod`); the bounded
`crossPattern_factor_of_upTo` is the finite-field-meaningful version.  The char-0 EGF identity
`F_G = F_H²` and `N₀(μ_n,2r) = (2r)!·[x^{2r}] I₀(2x)^{n/2}` are commentary. -/
theorem crossPattern_factored_summand {H : Finset F} {ζ : F} (hfac : DyadicFactorizes H ζ)
    (r s : ℕ) :
    Nat.choose r s * crossPattern H ζ (r - s) s
      = Nat.choose r s * (N0 H (r - s) * N0 H s) := by
  rw [crossPattern_factor hfac]

/-- **The convolution lower bound is at least the diagonal floor (consistency check).**  The two
endpoint terms of the factorised convolution sum to `2·N₀(H,r)` (`endpoints_sum_eq_diagonal`),
matching `CumulantDyadicDescent.N0_dyadic_descent_ge`.  The full convolution adds the
(nonnegative) interior terms — which under a factorisation gate are `C(r,s)N₀(H,s)N₀(H,r−s)`;
the split itself is not formalized here. -/
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
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.crossPattern_factor_of_upTo
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.not_dyadicFactorizes_zmod
#print axioms ArkLib.ProximityGap.CumulantDyadicConvolution.not_dyadicFactorizes_thin_example
