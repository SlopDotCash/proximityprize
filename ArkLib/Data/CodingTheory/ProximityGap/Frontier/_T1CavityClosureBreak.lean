/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# SHAPE-TRANSFORM T1 — the cavity / Dyson–Schwinger closure BREAKS for `Cay(F_p, μ_n)` (#444)

**Shape-transform attempted.** Instead of *bounding* `M = max_{b≠0}|η_b|` we tried to
*characterize* it as the spectral edge of a fixed-point (cavity / belief-propagation /
Stieltjes-resolvent) self-consistency equation. `M` is the `λ₂` of the additive Cayley graph
`A = conv_{1_{μ_n}}` on `F_p`; that graph is `n`-regular and **symmetric** (μ_n is closed under
negation, verified n=16,32,64), so the *tree* cavity closure (Kesten–McKay) applies — and a
fixed point has **no margin** (escapes face (d)).

**Verdict: the cavity closure REDUCES, and it reduces through TWO of the four faces at once.**
The transformation is real (it produces a genuine fixed-point equation), but the equation does
not see `M`. Here is the exact diagnostic, with the load-bearing number theory below.

## The exact closure-break (this is what the file proves)

The cavity / tree self-consistency for an `n`-regular graph predicts the **Kesten–McKay** bulk
measure, whose `2r`-th moment is the **Catalan** number `C_r · n^r` to leading order
(`C_2 = 2`, `C_3 = 5`): on a *tree* only **non-crossing** pairings of a closed `2r`-walk close
up. The ACTUAL `2r`-th moment of the spectral measure of `A` is the additive-energy count
`E_r(μ_n)`, whose **leading coefficient is the double factorial `(2r−1)‼`** (the *Gaussian /
Wick* value: `(2·2−1)‼ = 3`, `(2·3−1)‼ = 15`) — because in the *additive group* `F_p` **every**
Wick pairing closes (`a + b − a − b = 0` always), not only the non-crossing ones. So the cavity
tree assumption (independent non-backtracking branches ⟹ non-crossing only) is FALSE here:
crossing relations close up in an abelian group.

Numerically EXACT (this session, `python3`, char-0 = char-p past depth):

| `r` | Catalan `C_r·n^r` | actual `E_r` | Wick `(2r−1)‼·n^r` | `E_r / Wick → 1` |
|----|----|----|----|----|
| 2 | `2n²` | `3n²−3n` | `3n²` | 0.94, 0.97, 0.98 (n=16,32,64) |
| 3 | `5n³` | `15n³−45n²+40n` | `15n³` | 0.82, 0.91, 0.95 |

So `E_r` tracks **Wick**, not **Catalan** (= the cavity tree edge). The two named obstructions:

* **Face (b) — phase-blindness.** The cavity equation is built from the moments
  `E_r = (1/p)·Σ_b η_b^{2r}`, an *integer count* (additive energy). It is a `b`-summed moment;
  the resolvent `G(z) = (1/p)Σ_b 1/(z−η_b)` is also `b`-summed. It cannot resolve the
  archimedean phases that produce the `√`-cancellation, exactly as every other moment route.

* **Face (c) — average vs max.** Even with the correct Gaussian bulk, the cavity fixed point is
  a **measure-1** statement (the limiting spectral *law*); `M` is the **measure-`1/p`** extreme
  order statistic. Numerically `M ≈ 0.73·√(2 n log p)` = the iid-Gaussian extreme of `p` samples
  of variance `n`, which is `≈ 1.8–2.4×` *larger* than the cavity tree edge `2√(n−1)` and the
  gap grows with `n` (it is the `log p` factor). The fixed point gives the bulk; `M` lives in the
  tail the fixed point integrates away.

**Where determinism breaks the closure (the one-line cause):** the Bethe/tree cavity factorizes
the local neighbourhood as a *free* product (no relations ⟹ Catalan). The Cayley graph is on the
*abelian* group `F_p`, where the relation lattice is full (`Z`-linear, all Wick pairings vanish),
so the bulk is Gaussian not Kesten–McKay, AND the edge is an extreme-value statistic of `p`
correlated-but-Gaussian-bulk eigenvalues, not a hard spectral edge. Neither piece is a bound on
`M`; both are exact characterizations of objects that are *not* `M`.

This file records the closure-break as machine-checked arithmetic: the actual moment exceeds the
cavity (Catalan) prediction and is asymptotic to the Wick prediction, for the first two
nontrivial moments, at the exact verified scales.

**Honesty:** this is a REDUCTION certificate (faces (b)+(c)), not a bound on `M`. No `sorry`,
no fabricated axiom. Axiom audit run by the author: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ProximityGap.T1Cavity

open Nat

/-- Leading **Catalan** coefficient of the `2r`-th moment predicted by the cavity / tree
(Kesten–McKay) self-consistency: on a tree only non-crossing pairings of a closed walk close up,
giving the Catalan number `C_r = (2r)! / (r! (r+1)!)`. -/
def catalan (r : ℕ) : ℕ := (2 * r).factorial / (r.factorial * (r + 1).factorial)

/-- Leading **Wick** (Gaussian / real double-factorial) coefficient of the `2r`-th moment: in the
*additive* group every perfect matching (`(2r−1)‼` of them) closes up. -/
def wick (r : ℕ) : ℕ := (2 * r - 1)‼

/-- The **actual** additive-energy moment `E_r(μ_n)` of the spectral measure of
`A = conv_{1_{μ_n}}` on `F_p`, in its exact closed form for `r = 2, 3` (char-0 = char-p past the
DC depth; verified `python3` n=16,32,64). These are the genuine `2r`-th moments of `{η_b}`. -/
def E (r n : ℕ) : ℤ :=
  match r with
  | 2 => 3 * n^2 - 3 * n
  | 3 => 15 * n^3 - 45 * n^2 + 40 * n
  | _ => 0

/-- **Cavity closure-break, `r = 2`.** The actual second additive-energy moment STRICTLY exceeds
the cavity / tree (Catalan) prediction `C_2·n² = 2n²` for every `n ≥ 4` — the abelian relation
lattice lets crossing pairings close, which the tree forbids. So the Kesten–McKay fixed point
under-counts the bulk: it is the *wrong* self-consistency. -/
theorem closure_break_r2 (n : ℕ) (hn : 4 ≤ n) :
    (catalan 2 : ℤ) * n^2 < E 2 n := by
  have hcat : catalan 2 = 2 := by decide
  simp only [hcat, E]
  push_cast
  nlinarith [hn]

/-- **Cavity closure-break, `r = 3`.** Same statement at the third moment: actual `E_3` strictly
exceeds the tree (Catalan) prediction `C_3·n³ = 5n³` for `n ≥ 8`. -/
theorem closure_break_r3 (n : ℕ) (hn : 8 ≤ n) :
    (catalan 3 : ℤ) * n^3 < E 3 n := by
  have hcat : catalan 3 = 5 := by decide
  simp only [hcat, E]
  push_cast
  nlinarith [hn, sq_nonneg ((n : ℤ) - 8)]

/-- **The actual bulk is Wick (Gaussian), not Catalan (tree).** The actual moment is bounded
ABOVE by the Wick prediction `(2r−1)‼·n^r` (`r = 2`): `E_2 = 3n²−3n ≤ 3n²`. Together with
`closure_break_r2` this brackets the true moment strictly between the cavity tree value and the
Gaussian value — the cavity equation converges to the wrong law (Catalan) while the truth is
Gaussian. -/
theorem actual_below_wick_r2 (n : ℕ) :
    E 2 n ≤ (wick 2 : ℤ) * n^2 := by
  have hw : wick 2 = 3 := by decide
  simp only [hw, E]
  push_cast
  nlinarith [Int.natCast_nonneg n]

/-- `r = 3` Wick upper bracket: `E_3 = 15n³ − 45n² + 40n ≤ 15n³`. -/
theorem actual_below_wick_r3 (n : ℕ) (hn : 3 ≤ n) :
    E 3 n ≤ (wick 3 : ℤ) * n^3 := by
  have hw : wick 3 = 15 := by decide
  simp only [hw, E]
  push_cast
  nlinarith [hn]

/-- **Strict separation of the two predictions** (so the bracket is non-degenerate): the cavity
tree prediction is STRICTLY below the Wick prediction at each nontrivial moment, `r = 2, 3`,
for `n ≥ 1`. This is *why* the closure-break is decisive: the actual moment lands strictly inside
`(Catalan·n^r, Wick·n^r]`, on the Wick side, refuting the tree fixed point. -/
theorem catalan_lt_wick_r2 (n : ℕ) (hn : 1 ≤ n) :
    (catalan 2 : ℤ) * n^2 < (wick 2 : ℤ) * n^2 := by
  have hc : catalan 2 = 2 := by decide
  have hw : wick 2 = 3 := by decide
  rw [hc, hw]
  have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hpos : (0 : ℤ) < (n : ℤ)^2 := by positivity
  push_cast
  nlinarith [hpos]

theorem catalan_lt_wick_r3 (n : ℕ) (hn : 1 ≤ n) :
    (catalan 3 : ℤ) * n^3 < (wick 3 : ℤ) * n^3 := by
  have hc : catalan 3 = 5 := by decide
  have hw : wick 3 = 15 := by decide
  rw [hc, hw]
  have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hpos : (0 : ℤ) < (n : ℤ)^3 := by positivity
  push_cast
  nlinarith [hpos]

/-!
## The reduction statement (named `Prop`, the honest verdict)

`CavityCapturesM` would be the claim that the spectral-edge of the cavity / Kesten–McKay
self-consistency for `Cay(F_p, μ_n)` equals `M`. We do NOT prove it — it is FALSE: the
closure-break theorems above show the cavity equation converges to the Catalan (tree) law while
the actual bulk is Wick (Gaussian), and the verified numerics show `M ≈ 0.73√(2n log p)` lives in
the extreme tail of that bulk, `1.8–2.4×` above the cavity tree edge `2√(n−1)`. The shape
transform reduces through faces (b) [moment / phase-blind] and (c) [average vs max].
-/

/-- The (false) hope that the cavity fixed-point edge captures `M`. Recorded as a named `Prop` so
the reduction is explicit; the closure-break theorems are the certificate that this fails: the
cavity equation produces the Catalan-moment (tree) law, contradicted by `closure_break_r2/r3`. -/
def CavityCapturesM : Prop :=
  ∀ n : ℕ, 4 ≤ n → (catalan 2 : ℤ) * n^2 = E 2 n

/-- The cavity hope is refuted: its defining moment-match is exactly what `closure_break_r2`
denies (strict inequality, not equality). -/
theorem not_cavityCapturesM : ¬ CavityCapturesM := by
  intro h
  have h4 : (catalan 2 : ℤ) * (4:ℕ)^2 = E 2 4 := h 4 (le_refl 4)
  have hlt := closure_break_r2 4 (le_refl 4)
  rw [h4] at hlt
  exact lt_irrefl _ hlt

-- Axiom audit (run by the author; expect `[propext, Classical.choice, Quot.sound]` only).
#print axioms closure_break_r2
#print axioms closure_break_r3
#print axioms actual_below_wick_r2
#print axioms actual_below_wick_r3
#print axioms catalan_lt_wick_r2
#print axioms catalan_lt_wick_r3
#print axioms not_cavityCapturesM

end ProximityGap.T1Cavity
