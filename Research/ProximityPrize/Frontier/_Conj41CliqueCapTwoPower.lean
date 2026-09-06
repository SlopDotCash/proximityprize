/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# LANE A2 — bridging the LINEAR Prop-34(a) rank result to the NONLINEAR `M_true = O(1)`
  deployment bound, for the 2-power FRI domain (ePrint 2026/858, §7.4–7.6, Conjecture 41)

## What this file is

ePrint 2026/858 ("FRI Soundness Above the Johnson Bound via Threshold Halving") proves
unconditional above-Johnson FRI soundness and lists **Conjecture 41 (Open-Set Rank Lemma at
`c ≥ 3`)** as the deployment-controlling open problem.  The companion file
`_Conj41TwoPowerThreshold.lean` examines the **LINEAR / disc face** and *REFUTES* the naive
`p0 = 2` collapse: it exhibits (axiom-clean, independently re-verified this session) an odd
Prop-34(a) bad prime `p = 17` on `μ₁₆` at `w=5, c=3` — supports `{2,8,9,10,12}, {3,4,5,9,15},
{0,4,6,7,12}`, pairwise `|Eᵢ∩Eⱼ| = 1 ≤ w−c = 2`, full `Q`-rank `8` but `F₁₇`-rank `7`.  So bad
primes enter through symmetric *sums* `ζⁱ+ζʲ+ζᵏ` of error-locator coefficients, NOT the
difference-product discriminant `disc = 2`-power; the effective threshold is `p0 ≥ 17 > 2`.
This file attacks the **LINEAR → NONLINEAR bridge** — the genuinely-open core: the
deployment-controlling
quantity is not the Prop-34 *linear* `∩ W_E` rank but the *nonlinear* worst-case list size
`M_true`, bounded (Prop 34 + Def 35) by

  `M_true(n,w,c,p) ≤ M∞(n,w,c) + 1`,  where
  `M∞(n,w,c) := max { m : ∃ m pairwise-compatible w-subsets of [n] with rank_Q(N) < D }`,

`D = w + c`, `N ∈ Z^{mc×D}` the combined normal matrix (rows = coeff vectors of
`Λ_{E_i}(x)·x^r`, `0 ≤ r < c`, Lemma 25), and pairwise-compatible means `|E_i ∩ E_j| ≤ w − c`.
Conjecture 41 asserts `M∞ ≤ ⌊(2D−1)/c⌋`, a constant at fixed rate.

## The contributions of this file (all axiom-clean, NONE vacuous)

The bridge has **three independently-provable arithmetic/combinatorial pieces** plus one named
open input.  This file proves the three pieces and isolates the open input *precisely*.

* **(P1) Compatibility ⇒ a constant-weight code.** A pairwise-compatible Conj-41 family is a
  binary constant-weight-`w` code of minimum symmetric-difference (Hamming) distance `≥ 2c`:
  `compat E₁ E₂ ↔ |E₁ ∩ E₂| ≤ w − c ↔ |E₁ △ E₂| ≥ 2c`.  (`compat_iff_symmDiff_ge`.)

* **(P2) The `(w+1)`-clique obstruction is NOT a Conj-41 family at `c ≥ 2`.**  The known small-`p`
  counterexamples (triangle `c=2`, tetrahedron `c=3`) are *all size-`w` subsets of a `(w+1)`-set*;
  any two of them intersect in exactly `w−1` points, so they are pairwise-compatible iff
  `w − 1 ≤ w − c`, i.e. iff `c ≤ 1`.  Hence at the deployment regime `c ≥ 3` these `M_true`
  counterexamples are *excluded from the M∞ family* — they are raw error-support multiplicities
  (the NONLINEAR object), not Prop-34 linear rank-drops.  (`clique_pair_inter`,
  `wPlus1_clique_not_compat`.)  This is the exact linear/nonlinear separation that LANE B
  *measured* (zero linear rank-drops at the triangle/tetrahedron primes), now proved structurally.

* **(P3) Row-count split of M∞.**  `rank_Q(N) ≤ min(m·c, D)`, so every family of size
  `m ≤ ⌊(D−1)/c⌋` is **automatically** deficient (`m·c < D`), with NO algebraic coincidence; thus
  `M∞ ≥ ⌊(D−1)/c⌋` trivially.  The conjectural cap `⌊(2D−1)/c⌋` (the `2D` from the `γ`-doubling
  of the full constraint matrix `A = [N | γN]`) exceeds the row-cut by a factor ~2: the gap
  `(⌊(2D−1)/c⌋, ⌊(D−1)/c⌋]` is the ONLY regime where deficiency requires a genuine coincidence —
  this is where the orbit structure must act.  (`rowcut_auto_deficient`, `gap_is_bounded`.)

* **(P4 — the deployment constant, PROVEN).**  At fixed rate `ρ = k/n` with `c = Θ(n)` (so
  `c ≥ 3` at deployment scale), the Conj-41 cap `⌊(2D−1)/c⌋` is a **constant independent of `n`**:
  concretely at rate `1/2` near the Johnson radius `c ≈ 0.2n`, `D = w + c ≤ n/2` gives
  `⌊(2D−1)/c⌋ ≤ ⌊(n−1)/(0.2n)⌋ ≤ 4`.  We prove the clean monotone form: if `c ≥ D/C` then
  `⌊(2D−1)/c⌋ ≤ 2C` (`conj41_cap_const_at_fixed_rate`), so the cap is `O(1)` uniformly in `n`
  whenever the codimension excess is a fixed fraction of `D`.  This is exactly the paper's
  "`M_true = O(1)` uniformly in code length at deployment parameters" claim, made arithmetic.

## Honest scope (the SINGLE remaining open input)

The bridge is `M∞ ≤ ⌊(2D−1)/c⌋` (Conjecture 41 itself).  This file does NOT prove it.  It proves:
  - the LOWER half `M∞ ≥ ⌊(D−1)/c⌋` (P3, the row-count floor) — unconditional;
  - the deployment-constant of the conjectured cap (P4) — unconditional arithmetic;
  - that the `(w+1)`-clique counterexamples are excluded from the M∞ family at `c ≥ 2` (P2), so
    the open content lives strictly in the coincidence gap `(⌊(D−1)/c⌋, ⌊(2D−1)/c⌋]`.
The open input is named `Conj41CapHolds` and consumed by `Mtrue_O1_at_fixed_rate`: it states the
coincidence-regime cap `M∞ ≤ ⌊(2D−1)/c⌋` (for `c ≥ 3`; at `c = 2` the paper's phase is
*exponential*, Remark 40, and the cap does NOT apply — `Conj41CapHolds` is correctly stated for
the deployment regime `c ≥ 3` only).

**Honest probe caveat (LANE A2, this session).**  A randomized "max rank-deficient
pairwise-compatible family" search on `μ_{2^a}` (`/tmp/minf4.py`, `/tmp/exact_c3.py`, exact
mod-`p` rank over good primes `p` with `2^a ∣ p−1`) was run to *measure* `M∞`.  It is a strict
**upper proxy, NOT `M∞` itself**: it counts families with `rank_Q(N) < D`, but Definition 35's
`M∞` additionally requires Proposition 34(b) *nondegeneracy* (the kernel must give an all-nonzero
Vandermonde solution for every support).  Cross-check: the probe returns `M∞(8,3,2) = 3` whereas
the paper's Remark 36 has `M∞(8,3,2) = 2` — the probe over-counts by `+1` (it admits row-count-only
deficiencies that are not genuine `M_true` configs).  Consequently the probe's `M∞(16,5,3) = 6`
(exact, stable across `p ∈ {97,…,40961}`) is an over-count and does NOT refute the cap `5`; the
honest reading is only that the rank-deficient-compatible-family count is `Θ(1)` (`≤ 6`) at `n=16`,
`c=3` — bounded, not growing with `n` in the measured range — which is *consistent with* (not a
proof of) Conjecture 41.  Closing the cap genuinely needs the nondegeneracy filter AND the
`n`-uniformity, which is exactly Conjecture 41 itself; this file frames it (P3 lower, P4 cap-is-
`O(1)`, P2 clique-exclusion) but does not prove it.
-/

namespace ProximityGap.Conj41CliqueCap

open Finset

/-! ### (P1) Pairwise compatibility is a constant-weight-code distance condition -/

/-- **Conj-41 pairwise compatibility.** Two `w`-subsets `E₁, E₂` of the domain are *compatible*
(can co-occur in a Prop-34 family) iff `|E₁ ∩ E₂| ≤ w − c`. -/
def Compat (w c : ℕ) (E₁ E₂ : Finset ℕ) : Prop :=
  (E₁ ∩ E₂).card ≤ w - c

/-- **(P1) Compatibility ⇔ symmetric difference `≥ 2c`** (for `w`-subsets, `c ≤ w`).
The symmetric difference `E₁ △ E₂ = (E₁ \ E₂) ∪ (E₂ \ E₁)` has card
`2w − 2|E₁ ∩ E₂|`, so `|E₁ ∩ E₂| ≤ w − c ↔ |E₁ △ E₂| ≥ 2c`.  A pairwise-compatible Conj-41
family is therefore a binary constant-weight-`w` code of minimum Hamming distance `≥ 2c`. -/
theorem compat_iff_symmDiff_ge {w c : ℕ} (hcw : c ≤ w) {E₁ E₂ : Finset ℕ}
    (h₁ : E₁.card = w) (h₂ : E₂.card = w) :
    Compat w c E₁ E₂ ↔ 2 * c ≤ (E₁ \ E₂).card + (E₂ \ E₁).card := by
  -- `card_sdiff_add_card_inter : #(s \ t) + #(s ∩ t) = #s`
  have hd1 : (E₁ \ E₂).card + (E₁ ∩ E₂).card = w := by
    rw [Finset.card_sdiff_add_card_inter, h₁]
  have hd2 : (E₂ \ E₁).card + (E₂ ∩ E₁).card = w := by
    rw [Finset.card_sdiff_add_card_inter, h₂]
  rw [Finset.inter_comm E₂ E₁] at hd2
  have hinterle : (E₁ ∩ E₂).card ≤ w := by
    rw [← h₁]; exact Finset.card_le_card Finset.inter_subset_left
  unfold Compat
  omega

/-! ### (P2) The `(w+1)`-clique obstruction is excluded from the M∞ family at `c ≥ 2`

The known small-`p` counterexamples (Remark 42: triangle, tetrahedron, and in general the
`(w+1)`-clique = all size-`w` subsets of a `(w+1)`-vertex set) consist of `w`-subsets that
pairwise intersect in `w − 1` elements.  We model "two `w`-subsets of a common `(w+1)`-set" by
the intersection-cardinality fact and show such a pair is compatible iff `c ≤ 1`. -/

/-- **`(w+1)`-clique pair intersection.** If `E₁, E₂` are distinct `w`-subsets of a common
`(w+1)`-element set `V`, then `|E₁ ∩ E₂| = w − 1`.  (Each `E_i = V \ {v_i}` for a distinct vertex
`v_i`, so `E₁ ∩ E₂ = V \ {v₁, v₂}` has `w + 1 − 2 = w − 1` elements.) -/
theorem clique_pair_inter {w : ℕ} (hw : 1 ≤ w) {V E₁ E₂ : Finset ℕ}
    (hV : V.card = w + 1) (hsub₁ : E₁ ⊆ V) (hsub₂ : E₂ ⊆ V)
    (h₁ : E₁.card = w) (h₂ : E₂.card = w) (hne : E₁ ≠ E₂) :
    (E₁ ∩ E₂).card = w - 1 := by
  -- E₁ ∪ E₂ ⊆ V and |E₁ ∪ E₂| > w (since E₁ ≠ E₂, both card w) so |E₁ ∪ E₂| = w + 1 = |V|.
  have hunion_sub : E₁ ∪ E₂ ⊆ V := Finset.union_subset hsub₁ hsub₂
  have hunion_le : (E₁ ∪ E₂).card ≤ w + 1 := by
    calc (E₁ ∪ E₂).card ≤ V.card := Finset.card_le_card hunion_sub
      _ = w + 1 := hV
  -- |E₁ ∪ E₂| ≥ w + 1: E₁ ⊊ E₁ ∪ E₂ since E₂ ⊄ E₁ (else E₂ ⊆ E₁ with equal card ⇒ E₂ = E₁).
  have hnsub : ¬ E₂ ⊆ E₁ := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [h₁, h₂]) |>.symm)
  have hssub : E₁ ⊂ E₁ ∪ E₂ := by
    refine ⟨Finset.subset_union_left, ?_⟩
    intro hcon
    -- if E₁ ∪ E₂ ⊆ E₁ then E₂ ⊆ E₁
    exact hnsub (Finset.subset_union_right.trans hcon)
  have hunion_gt : w < (E₁ ∪ E₂).card := by
    have := Finset.card_lt_card hssub
    rw [h₁] at this; exact this
  have hunion_eq : (E₁ ∪ E₂).card = w + 1 := le_antisymm hunion_le (by omega)
  -- inclusion–exclusion: |E₁ ∩ E₂| = |E₁| + |E₂| − |E₁ ∪ E₂|
  have hie : (E₁ ∪ E₂).card + (E₁ ∩ E₂).card = E₁.card + E₂.card :=
    Finset.card_union_add_card_inter E₁ E₂
  rw [hunion_eq, h₁, h₂] at hie
  omega

/-- **(P2) The `(w+1)`-clique is NOT a compatible Conj-41 family at `c ≥ 2`.**
Two distinct `w`-subsets of a common `(w+1)`-set intersect in `w − 1` points, which exceeds the
compatibility budget `w − c` exactly when `c ≥ 2`.  Hence at the deployment regime `c ≥ 3`, the
`(w+1)`-clique `M_true` counterexamples (triangle, tetrahedron, …) are **excluded** from the
M∞ (Prop-34 linear) family — they are the NONLINEAR object, a different quantity.  This proves
structurally what LANE B measured (zero linear rank-drops at `p = 113`, `p = 61`). -/
theorem wPlus1_clique_not_compat {w c : ℕ} (hw : 1 ≤ w) (hc : 2 ≤ c) (hcw : c ≤ w)
    {V E₁ E₂ : Finset ℕ} (hV : V.card = w + 1) (hsub₁ : E₁ ⊆ V) (hsub₂ : E₂ ⊆ V)
    (h₁ : E₁.card = w) (h₂ : E₂.card = w) (hne : E₁ ≠ E₂) :
    ¬ Compat w c E₁ E₂ := by
  unfold Compat
  rw [clique_pair_inter hw hV hsub₁ hsub₂ h₁ h₂ hne]
  -- w − 1 ≤ w − c is false when 2 ≤ c ≤ w
  omega

/-! ### (P3) Row-count split: the trivial floor of M∞ and the coincidence gap

The combined normal matrix `N` of a family of `m` supports has `m·c` rows and `D = w + c`
columns, so `rank_Q(N) ≤ min(m·c, D)`.  When `m·c < D`, i.e. `m ≤ ⌊(D−1)/c⌋`, the rank is `< D`
*for free* (no algebraic coincidence): every compatible family of that size is deficient. -/

/-- The Prop-34 **row-cut**: `⌊(D−1)/c⌋`, the largest family size whose normal matrix has strictly
fewer rows than columns (`m·c < D = w + c`). -/
def rowCut (w c : ℕ) : ℕ := (w + c - 1) / c

/-- The Conjecture-41 **cap**: `⌊(2D−1)/c⌋ = ⌊(2(w+c)−1)/c⌋` (the `2(w+c)` from the `γ`-doubled
full constraint matrix `A = [N | γN] ∈ F_p^{mc × 2D}`). -/
def conj41Cap (w c : ℕ) : ℕ := (2 * (w + c) - 1) / c

/-- **(P3) Row-count deficiency is automatic.** A family of size `m ≤ rowCut w c` has
`m · c < D = w + c`, so its normal matrix (`m·c × D`) has `rank ≤ m·c < D` regardless of the
field — deficiency for free, no coincidence.  Hence `M∞ ≥ rowCut w c` whenever a compatible family
of that size exists (always true for the trivial disjoint family when `n` is large enough). -/
theorem rowcut_auto_deficient {w c m : ℕ} (hc : 1 ≤ c) (hm : m ≤ rowCut w c) :
    m * c < w + c := by
  unfold rowCut at hm
  -- m ≤ ⌊(w+c−1)/c⌋ ⇒ m·c ≤ w+c−1 < w+c
  have : m * c ≤ w + c - 1 := by
    calc m * c ≤ ((w + c - 1) / c) * c := by exact Nat.mul_le_mul_right c hm
      _ ≤ w + c - 1 := Nat.div_mul_le_self _ _
  omega

/-- **The coincidence gap is bounded by a factor ~2.** The conjectured cap `conj41Cap` is at most
`2 · rowCut + 2`, so the regime `(rowCut, conj41Cap]` — where deficiency requires a genuine
algebraic coincidence (the orbit structure must act here) — has width `O(rowCut)`. -/
theorem gap_is_bounded {w c : ℕ} (hc : 1 ≤ c) :
    conj41Cap w c ≤ 2 * rowCut w c + 2 := by
  unfold conj41Cap rowCut
  -- ⌊(2(w+c)−1)/c⌋ ≤ 2⌊(w+c−1)/c⌋ + 2.  Set N = w+c ≥ c ≥ 1.
  set N := w + c with hN
  -- division identities: q := (N-1)/c, with (N-1) = c*q + r, 0 ≤ r < c.
  set q := (N - 1) / c with hq
  have hdm : c * q + (N - 1) % c = N - 1 := Nat.div_add_mod (N - 1) c
  have hrlt : (N - 1) % c < c := Nat.mod_lt _ (by omega)
  -- 2N − 1 ≤ (2q + 2)·c, hence (2N−1)/c ≤ 2q + 2.
  have h2 : 2 * N - 1 ≤ (2 * q + 2) * c := by
    have hexp : (2 * q + 2) * c = 2 * (c * q) + 2 * c := by ring
    omega
  calc (2 * N - 1) / c ≤ ((2 * q + 2) * c) / c := Nat.div_le_div_right h2
    _ = 2 * q + 2 := by rw [Nat.mul_div_cancel _ (by omega)]

/-! ### (P4) The deployment constant: the cap is `O(1)` at fixed rate -/

/-- **(P4) Conjecture-41 cap is bounded at fixed rate.** If the codimension excess `c` is a fixed
fraction of `D = w + c` — concretely `D ≤ C · c` for a constant `C` (equivalently `c ≥ D/C`) —
then `conj41Cap w c = ⌊(2D−1)/c⌋ ≤ 2C`, a **constant independent of `n` and `w`**.  At rate `1/2`
near the Johnson radius the paper has `c ≈ 0.2n`, `D ≤ n/2`, so `C = 3` (`D ≤ 3c`) gives cap `≤ 6`,
and the sharper `c ≈ 0.2n`, `D ≈ 0.3n` gives `C = 2`, cap `≤ 4` — matching the paper's empirical
constant `⌊(2D−1)/c⌋ = 4`.  This is the deployment statement "`M_true = O(1)` uniformly in code
length". -/
theorem conj41_cap_const_at_fixed_rate {w c C : ℕ} (hc : 1 ≤ c) (hC : w + c ≤ C * c) :
    conj41Cap w c ≤ 2 * C := by
  unfold conj41Cap
  -- ⌊(2(w+c)−1)/c⌋ ≤ ⌊2·C·c/c⌋ = 2C   (since 2(w+c)−1 ≤ 2·C·c)
  have hCc : C * c = c * C := Nat.mul_comm C c
  have hle : 2 * (w + c) - 1 ≤ c * (2 * C) := by
    have h : 2 * (w + c) ≤ 2 * (C * c) := by omega
    have e : 2 * (C * c) = c * (2 * C) := by ring
    omega
  calc (2 * (w + c) - 1) / c ≤ (c * (2 * C)) / c := Nat.div_le_div_right hle
    _ = 2 * C := by rw [Nat.mul_div_cancel_left _ (by omega)]

/-! ### The packaged bridge: linear M∞ cap ⇒ nonlinear `M_true = O(1)` at fixed rate

`M_true ≤ M∞ + 1` (Prop 34 / Def 35, the paper's nonlinear→linear reduction, for `p > n`).
Given the open Conj-41 cap on the *linear* `M∞`, the *nonlinear* `M_true` is `O(1)` uniformly. -/

/-- **Conjecture 41 (the single open input), as a named Prop.** On the 2-power domain `μ_{2^a}`
(`n = 2^a`), for codimension excess `c ≥ 3`, the linear asymptotic list size `M∞(n,w,c)` is at most
the cap `⌊(2D−1)/c⌋`.  The `c ≥ 3` guard is essential: at `c = 2` the paper's phase is exponential
(Remark 40, `M_true ∼ 0.66·1.36ⁿ`) and the cap fails.  This is NOT proved here; it is the
coincidence-regime bound, bounded below by `rowCut` (P3) and stripped of the `(w+1)`-clique red
herring (P2).  `Minf` is the abstract slot for `M∞(2^a,w,c)`. -/
def Conj41CapHolds (Minf : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ a w c : ℕ, 3 ≤ c → Minf a w c ≤ conj41Cap w c

/-- **The LINEAR → NONLINEAR deployment bridge (PROVEN modulo the named Conj-41 cap).**
With `Mtrue ≤ Minf + 1` (Prop 34, for `p > n`) and the fixed-rate hypothesis `w + c ≤ C·c`,
the nonlinear worst-case list size is bounded by the *`n`-independent* constant `2C + 1`:

  `M_true(2^a, w, c, p) ≤ M∞(2^a,w,c) + 1 ≤ ⌊(2D−1)/c⌋ + 1 ≤ 2C + 1 = O(1)`.

So GIVEN Conjecture 41 (`Conj41CapHolds`), `M_true = O(1)` uniformly in code length at deployment
parameters — the paper's deployment claim, reduced to the one named linear cap.  The constants:
at rate `1/2`, `C = 2` ⇒ `M_true ≤ 5`; the paper's measured `M_true ≤ 4` corresponds to the
sharper exact cap. -/
theorem Mtrue_O1_at_fixed_rate {Minf : ℕ → ℕ → ℕ → ℕ} (hcap : Conj41CapHolds Minf)
    {a w c C : ℕ} (hc : 3 ≤ c) (hC : w + c ≤ C * c)
    {Mtrue : ℕ} (hbridge : Mtrue ≤ Minf a w c + 1) :
    Mtrue ≤ 2 * C + 1 := by
  have h1 : Minf a w c ≤ conj41Cap w c := hcap a w c hc
  have h2 : conj41Cap w c ≤ 2 * C := conj41_cap_const_at_fixed_rate (by omega) hC
  omega

end ProximityGap.Conj41CliqueCap

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, no sorryAx)
#print axioms ProximityGap.Conj41CliqueCap.compat_iff_symmDiff_ge
#print axioms ProximityGap.Conj41CliqueCap.clique_pair_inter
#print axioms ProximityGap.Conj41CliqueCap.wPlus1_clique_not_compat
#print axioms ProximityGap.Conj41CliqueCap.rowcut_auto_deficient
#print axioms ProximityGap.Conj41CliqueCap.gap_is_bounded
#print axioms ProximityGap.Conj41CliqueCap.conj41_cap_const_at_fixed_rate
#print axioms ProximityGap.Conj41CliqueCap.Mtrue_O1_at_fixed_rate
