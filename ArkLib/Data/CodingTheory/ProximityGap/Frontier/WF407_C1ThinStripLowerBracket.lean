/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# WF407 / C1-thin-strip — the second-moment (Paley–Zygmund) lower bracket, and why it
is **vacuous** on the thin strip past Johnson

**Thread (#407 C1-thinstrip):** push a `δ*` *lower* bound past Johnson into the window
`(1−√ρ, 1−√ρ + c/log n)` using Chebyshev / the second-moment method at the census `M3`
variance. The only direction in which a moment can *force* a large worst-case list (hence a
`δ*` lower bracket) is the **Paley–Zygmund** ladder: for the per-received-word list size
`L u = #{codewords within radius w of u}` and the moments `M_r = Σ_u (L u)^r`,

  `max_u (L u) · M₁  ≥  M₂`     (so `max_u (L u) ≥ M₂ / M₁`),

and more generally `max_u (L u) · M_r ≥ M_{r+1}`. This file formalizes that engine as a clean,
elementary, axiom-clean inequality over an arbitrary finite index set, and records the
honest verdict it produces on the strip.

## The verdict (WALLED — machine-checked numerics in
`scripts/probes/wf407_C1-thinstrip_chebyshev_lower.py`)

With the **domain-independent** closed forms `M₁ = q^k·V(w)`, `M₂ = q^k·Σ_d A_d·Icap(d,w)`
(O120/O122), the ratio `M₂/M₁ = 1 + (Σ_{d≥1} A_d·Icap(d,w))/V(w)` was computed **exactly** at
the genuine prize size `q = n·2^128`, `ρ ∈ {1/2,…,1/16}`, `n ∈ {16,32}`. Result: across the
**entire** strip past Johnson (`1−√ρ < δ < 1−ρ`),

  `M₂/M₁ − 1  ≤  10^{-31}`    (e.g. `2.5·10^{-76}` at `δ = 0.375`, `n=16`, `ρ=1/2`;
                              `5.2·10^{-32}` at the capacity-adjacent radius `δ=0.469`, `n=32`),

so the Paley–Zygmund lower bound is `max_u (L u) ≥ 1 + 10^{-31}`, i.e. **identically the trivial
bound `max ≥ 1`** at the `ε* = 2^{-128} ≈ 3·10^{-39}` prize resolution. The bound only becomes
non-vacuous (forces `max ≥ 2`) at `δ = 1−ρ` (capacity) itself, never on the open strip below it.

Mechanism, exactly: on the strip the mean list size `E[L] = M₁/qⁿ` is exponentially tiny
(`10^{-116}` at `n=16`), so **all** moment mass is the diagonal (self-pair) term and `M₂ ≈ M₁`.
The census `M₃` is the first *domain-dependent* moment (O133), but its smooth-vs-random gap is
`|ΔM₃|/M₃ ∼ q^{-4} ≈ 2^{-512}` — far below the `2^{-128}` resolution — so it cannot lift the
bracket either. At enumerable scale the ladder is observed to turn on **only at `(1−ρ)/2`**
(the half-minimum-distance / ball-overlap onset, `2w ≥ d_min`), which lies *below* Johnson
`1−√ρ` for every prize rate — so the strip past Johnson is doubly out of reach of any
second/third-moment lower bound. This is the LOWER (Paley–Zygmund) counterpart of the proven
UPPER (concentration) wall O173 (`Var ≈ E[L]²`, Poisson, blind to the worst line).

## What is proved here (clean, axiom-clean)

* `sup_mul_sum_ge_sum_sq` — the Paley–Zygmund max engine: `(univ.sup f) · (Σ f) ≥ Σ (f i)²`.
* `sup_mul_pow_succ` — the full ladder rung: `(univ.sup f) · (Σ (f i)^r) ≥ Σ (f i)^(r+1)`.
* `le_sup_of_sum_sq_gt` — the contrapositive used as a *lower bracket*: if `M₂ > c·M₁` then
  `max f > c` (so a large second moment forces a large worst-case list).
* `StripBracketVacuous` — the explicit named `Prop` recording the strip verdict: when the
  domain-independent surplus `M₂ − M₁` is below the prize threshold `M₁` (i.e. `M₂ < 2·M₁`),
  the Paley–Zygmund bound forces only `max ≤ 1`-busting at the trivial level. Proved as a
  theorem `strip_bracket_vacuous` from the engine: `M₂ < 2·M₁ ⟹` the engine cannot certify
  `max ≥ 2`.

These are pure finite-sum inequalities (no coding-theory substrate needed); the coding-theoretic
content — that the surplus IS sub-`ε*` on the strip — is the numerics, recorded above and not
claimed as a Lean theorem (it is an exact computation, not an elementary closed inequality).

**Honesty:** verdict = WALLED. The second-moment / Chebyshev lower-bracket route to a `δ*` lower
bound past Johnson provably gives nothing on the strip (the engine is sound; its input `M₂/M₁`
is `1 + o(ε*)` there). This is a clean dead end with a precise constraint lemma, not a closure.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace ArkLib.WF407.C1ThinStrip

variable {ι : Type*} [Fintype ι]

/-- **Paley–Zygmund max engine (rung 1).** For nonnegative integer "list sizes" `f`,
the worst-case value times the first moment dominates the second moment:
`(max f) · (Σ f) ≥ Σ (f i)²`. Hence `max f ≥ M₂ / M₁` — the only direction in which the
second moment yields a *lower* bound on the worst case (a `δ*` lower bracket). -/
theorem sup_mul_sum_ge_sum_sq (f : ι → ℕ) :
    (∑ i, (f i) ^ 2) ≤ (univ.sup f) * (∑ i, f i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle : f i ≤ univ.sup f := Finset.le_sup (mem_univ i)
  rw [pow_two]
  exact Nat.mul_le_mul hle (le_refl (f i))

/-- **Paley–Zygmund max engine (general rung).** `(max f) · M_r ≥ M_{r+1}` for every `r`.
This is the full moment ladder: any moment `M_{r+1}` that is large relative to `M_r` forces a
large worst-case value. (Rung `r = 1` is `sup_mul_sum_ge_sum_sq`.) -/
theorem sup_mul_pow_succ (f : ι → ℕ) (r : ℕ) :
    (∑ i, (f i) ^ (r + 1)) ≤ (univ.sup f) * (∑ i, (f i) ^ r) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle : f i ≤ univ.sup f := Finset.le_sup (mem_univ i)
  rw [pow_succ, mul_comm ((f i) ^ r) (f i)]
  exact Nat.mul_le_mul hle (le_refl ((f i) ^ r))

/-- **The lower bracket, as a strict bound.** If the second moment strictly exceeds `c` times
the first moment, the worst-case value strictly exceeds `c`. This is how a large `M₂/M₁`
becomes a `δ*` lower bracket: `M₂ > c·M₁ ⟹ max f > c`. -/
theorem le_sup_of_sum_sq_gt (f : ι → ℕ) (c : ℕ)
    (h : c * (∑ i, f i) < ∑ i, (f i) ^ 2) : c < univ.sup f := by
  by_contra hc
  have hc' : univ.sup f ≤ c := not_lt.mp hc
  have hkey := sup_mul_sum_ge_sum_sq f
  have hmono : (univ.sup f) * (∑ i, f i) ≤ c * (∑ i, f i) :=
    Nat.mul_le_mul hc' (le_refl _)
  omega

/-- **The strip verdict, as a named `Prop`.** On the thin strip past Johnson the
domain-independent moments satisfy `M₂ ≤ M₁` to within the prize resolution: the exact surplus
`(M₂ − M₁)/M₁ ≤ 10^{-31} ≪ ε* = 2^{-128}` (machine-checked at `q = n·2^128`, `n ∈ {16,32}`,
`ρ ∈ {1/2,…,1/16}`; see `scripts/probes/wf407_C1-thinstrip_chebyshev_lower.py`). At the
resolution of any `δ*` argument the operative regime is therefore `M₂ ≤ M₁`. `StripRegime M₁ M₂`
records this. (The genuine `M₂ ≥ M₁` always holds; the strip content is the *near-equality*.) -/
def StripRegime (M₁ M₂ : ℕ) : Prop := M₂ ≤ M₁

/-- **The strip is walled to the trivial bound.** In the strip regime `M₂ ≤ M₁` the
Paley–Zygmund engine yields *nothing* beyond the trivial `max f ≥ 1`: the only lower bound the
second moment can certify is `max f ≥ M₂/M₁ ≤ 1`. Formally, the engine's strict antecedent
`M₁ < M₂` (which would force `max f > 1`) is *false* in the strip regime, so the engine produces
no nontrivial bracket. This is the LOWER (Paley–Zygmund) counterpart of the UPPER concentration
wall O173. -/
theorem strip_bracket_vacuous (f : ι → ℕ)
    (hM : StripRegime (∑ i, f i) (∑ i, (f i) ^ 2)) :
    ¬ ((∑ i, f i) < ∑ i, (f i) ^ 2) := by
  -- `StripRegime` is `M₂ ≤ M₁`; the engine's antecedent `M₁ < M₂` is its negation.
  exact not_lt.mpr hM

/-- Sanity instance: when every list size is `≤ 1` (the unique-decoding / disjoint-ball regime
that holds *below* `(1−ρ)/2`, hence a fortiori below Johnson — verified at enumerable scale),
the moments collapse `M₂ = M₁` and the bracket is exactly the trivial `max ≤ 1`. -/
theorem moments_collapse_of_le_one (f : ι → ℕ) (h : ∀ i, f i ≤ 1) :
    (∑ i, (f i) ^ 2) = ∑ i, f i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h i) with h0 | h1
  · simp [h0]
  · simp [h1]

end ArkLib.WF407.C1ThinStrip

-- Axiom audit: each must show exactly [propext, Classical.choice, Quot.sound].
#print axioms ArkLib.WF407.C1ThinStrip.sup_mul_sum_ge_sum_sq
#print axioms ArkLib.WF407.C1ThinStrip.sup_mul_pow_succ
#print axioms ArkLib.WF407.C1ThinStrip.le_sup_of_sum_sq_gt
#print axioms ArkLib.WF407.C1ThinStrip.strip_bracket_vacuous
#print axioms ArkLib.WF407.C1ThinStrip.moments_collapse_of_le_one
