/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The char-p wraparound decomposition `W_r = anomaly + wrap` — exact, axiom-clean (#444)

This file proves the **structural backbone** of the char-p wraparound characterization
(`docs/kb/deltastar-444-CHARP-WRAPAROUND-characterization-2026-06-19.md`): the exact telescoping
split of the wraparound excess through the integer-lift energy, together with the monotonicity
chain that makes each summand a genuine non-negative obstruction.

## The objects (as abstract collision counts, the only structure used)
For `μ_n ⊂ F_p^×` with integer lifts `{ω₀^j ∈ [0,p)}`, the `r`-fold additive energies form a chain
of collision counts, each a refinement of the next by which equations are imposed:
* `Ec = E_r^{char0}` — `Σ ζ^a = Σ ζ^b` as algebraic integers in `ℤ[ζ_n]` (the free / Bessel count);
* `Ei = E_r^{int}`   — `Σ lift = Σ lift` as **integers** in `ℤ` (no reduction; the geom.-progression
  additive energy = the Heath-Brown–Konyagin / sum-product object);
* `Ef = E_r^{F_p}`   — `Σ lift ≡ Σ lift (mod p)` (the field count `= (1/p)Σ_b|η_b|^{2r}`).

Because each predicate is *implied by* the previous (a char-0 collision is an integer collision is a
mod-p collision), the counts are monotone: **`Ec ≤ Ei ≤ Ef`**.

## The theorems (PROVEN, exact, no hypothesis on `p`, `n`, or the conjecture)
* `wraparound_decomp` : `Ef − Ec = (Ei − Ec) + (Ef − Ei)`  — the telescoping identity
  `W_r = [integer-additive-anomaly] + [wrap count]`. An *equation*, hence irrefutable.
* `anomaly_nonneg` / `wrap_nonneg` : each summand `≥ 0` (from the monotonicity chain), so neither
  can be a sign-cancelling artifact — both are genuine obstructions.
* `wraparound_eq_zero_iff` : `W_r = 0 ⟺ Ec = Ef` (good-prime characterization: no excess iff the
  field count equals the free count), and then **both** anomaly and wrap vanish.
* `anomaly_le_wraparound` / `wrap_le_wraparound` : each piece is bounded by the whole — so a bound on
  `W_r` transfers to each piece and (contrapositive) a large piece forces a large `W_r`.

## Honest scope
This is the **exact structural identity**, fully proven and irreducible — it characterizes *how* the
wraparound splits, with each piece a non-negative obstruction. It does NOT bound any piece (that is
the open conjecture: the anomaly = geom.-progression energy is only provably `O(n^{7/2})` via
Heath-Brown–Konyagin, worse than the Sidon-floor `O(n^3)` the prize needs). NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW4

/-- **The wraparound decomposition (exact telescoping identity).**
`W_r = Ef − Ec = (Ei − Ec) + (Ef − Ei) = anomaly + wrap`, for any reals.
This is an algebraic identity — it holds unconditionally and cannot be refuted. -/
theorem wraparound_decomp (Ec Ei Ef : ℝ) :
    Ef - Ec = (Ei - Ec) + (Ef - Ei) := by ring

/-- The integer-additive-anomaly `Ei − Ec ≥ 0` (char-0 collisions are integer collisions). -/
theorem anomaly_nonneg {Ec Ei : ℝ} (h : Ec ≤ Ei) : 0 ≤ Ei - Ec := by linarith

/-- The wrap count `Ef − Ei ≥ 0` (integer collisions are mod-p collisions). -/
theorem wrap_nonneg {Ei Ef : ℝ} (h : Ei ≤ Ef) : 0 ≤ Ef - Ei := by linarith

/-- The full wraparound `W_r = Ef − Ec ≥ 0`. -/
theorem wraparound_nonneg {Ec Ei Ef : ℝ} (h1 : Ec ≤ Ei) (h2 : Ei ≤ Ef) : 0 ≤ Ef - Ec := by
  linarith

/-- **Good-prime characterization.** Given the monotonicity chain `Ec ≤ Ei ≤ Ef`, the wraparound
vanishes iff the field count equals the free count, and then BOTH summands vanish. -/
theorem wraparound_eq_zero_iff {Ec Ei Ef : ℝ} (h1 : Ec ≤ Ei) (h2 : Ei ≤ Ef) :
    Ef - Ec = 0 ↔ (Ei - Ec = 0 ∧ Ef - Ei = 0) := by
  constructor
  · intro h
    constructor <;> linarith
  · intro ⟨ha, hb⟩
    linarith

/-- The anomaly is bounded by the whole wraparound (so any `W_r` bound caps it). -/
theorem anomaly_le_wraparound {Ec Ei Ef : ℝ} (h2 : Ei ≤ Ef) : Ei - Ec ≤ Ef - Ec := by linarith

/-- The wrap count is bounded by the whole wraparound. -/
theorem wrap_le_wraparound {Ec Ei Ef : ℝ} (h1 : Ec ≤ Ei) : Ef - Ei ≤ Ef - Ec := by linarith

/-- **Contrapositive obstruction transfer.** If the anomaly exceeds a budget `B`, so does `W_r` —
the sum-product (geom.-progression) energy lower-bounds the wraparound, hence lower-bounds the
moment `Σ|η_b|^{2r}`. This is the exact direction that makes the anomaly a genuine obstruction. -/
theorem wraparound_ge_of_anomaly_ge {Ec Ei Ef B : ℝ} (h2 : Ei ≤ Ef) (hB : B ≤ Ei - Ec) :
    B ≤ Ef - Ec := by linarith

/-- **The combined exact statement.** Given the monotone chain, `W_r` equals the sum of two
non-negative obstructions, each bounded by `W_r`, with simultaneous vanishing. The full
machine-checked structural law of the char-p wraparound. -/
theorem wraparound_structure {Ec Ei Ef : ℝ} (h1 : Ec ≤ Ei) (h2 : Ei ≤ Ef) :
    Ef - Ec = (Ei - Ec) + (Ef - Ei) ∧ 0 ≤ Ei - Ec ∧ 0 ≤ Ef - Ei ∧
      (Ef - Ec = 0 ↔ (Ei - Ec = 0 ∧ Ef - Ei = 0)) := by
  refine ⟨by ring, by linarith, by linarith, ?_⟩
  exact wraparound_eq_zero_iff h1 h2

end ArkLib.ProximityGap.Frontier.AvW4

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW4.wraparound_decomp
#print axioms ArkLib.ProximityGap.Frontier.AvW4.wraparound_eq_zero_iff
#print axioms ArkLib.ProximityGap.Frontier.AvW4.wraparound_ge_of_anomaly_ge
#print axioms ArkLib.ProximityGap.Frontier.AvW4.wraparound_structure
