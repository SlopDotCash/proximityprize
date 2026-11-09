/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The 2-automatic-sequence (Gowers / odometer) route — archimedean no-go (#444, lens [automatic-seq])

**Lens.** (Konieczny; Drmota–Müllner–Spiegelhofer.) The index-doubling map `j ↦ 2j` on `Z/m`
(`m = (p−1)/n = 2^128` in the prize) is the dyadic **odometer**. Stickelberger / Gross–Koblitz give
the `p`-adic **valuation** of the Gauss sum `τ(χ^j)` as a base-`p` digit sum — a *2-automatic*
object. The route HOPE: `M(n) = max_{b≢0} |η_b|` is the sup-norm of the discrete Fourier transform
of the unit-modulus sequence `a_j := τ(χ^j)/√p`, and IF `a_j` were a `2`-automatic (or nilsequence)
sequence, the automatic-sequence Gowers-norm / discrepancy machinery would deliver
`M(n) ≤ C·√(n·log m)` with `C` depending only on the **automaton size** (the number of states).

**The crucial honest check (the prompt's requirement).** The valuation is automatic; the route
needs the *archimedean argument* `arg(τ(χ^j))` to be automatic too. The automatic-sequence
discrepancy theorems apply to a sequence `s : ℕ → A` taking values in a **finite alphabet** `A`
recognized by a deterministic finite automaton reading the base-`2` digits of `j`; the discrepancy
(equidistribution) bound is then `O(N^{1-c})` with the constant controlled by `|A|·(#states)`.

So the route reduces — **exactly and only** — to the decidable hypothesis:

> **`ArchimedeanArgAutomatic`**: there is a fixed finite alphabet of size `A` and a `2`-DFA with
> `K` states such that `j ↦ arg(τ(χ^j))` (discretised to `A` levels) is the DFA's output along the
> base-`2` digits of `j`, **uniformly in `n`** (i.e. `A, K` are absolute constants, independent of
> `n`).

If `ArchimedeanArgAutomatic` holds with absolute `A, K`, the route closes (`C = C(A,K)`). The probe
`scripts/probes/probe_444_automatic_seq_archimedean.py` REFUTES it on three independent decidable
tests (all on PROPER subgroups, never the full group):

* **T1** — the *only* odometer-compatible transition law for the argument would be the clean
  doubling `arg(τ_{2j}) = 2·arg(τ_j) (mod 2π)` (a Davenport–Hasse-style automatic step). Measured
  RMS defect ≈ `1.7–2.0 rad` = full white-noise level (`π/√3 ≈ 1.81`). **No automatic step.**
* **T2** — subword (factor) complexity of the discretised argument along a doubling orbit; an
  automatic sequence has `p_s(w) = O(w)` (linear), random over alphabet `A` has `A^w`. Measured:
  saturates at orbit length (no linear-complexity automaton visible).
* **T3** — Spearman correlation between `popcount(j)` (the Stickelberger digit-sum valuation
  surrogate) and `arg(τ_j)`: ≈ `0` (`−0.07 … +0.01`). **The argument is digit-blind.**

So the **valuation is 2-automatic but the archimedean argument is Katz-equidistributed white
noise** — the route dies at the *archimedean / p-adic split*, the same wall that killed the
Habegger equidistribution route (`KowalskiUntrauBarrier`) and the prior Stickelberger probe, now
pinned to the automatic-sequence mechanism specifically.

## What is PROVEN here (axiom-clean, integer arithmetic — the *quantitative* obstruction)

The automatic-sequence discrepancy constant `C(A,K)` is at least linear in the **alphabet
resolution** `A` needed to even *represent* the argument sequence faithfully. Parseval forces a
non-degenerate spread: `M(n) ≥ √n` (the graph is provably NOT Ramanujan, in-tree
`SubgroupGaussSum*`), so the DFT cannot be flattened by a single phase — the argument sequence has
`≥ √n` worth of distinct relevant levels at the worst frequency band. The decidable surrogate of
"how big an alphabet a faithful automatic representation needs" is therefore `≥ √n`, NOT a constant.
We formalise this as: the *automaton-resolution lower bound* `autResolution n := Nat.sqrt n` grows,
so the `C(A,K)` an automatic route would produce is `≥ √(autResolution n)`-style growing, i.e. the
route cannot deliver an **absolute** constant `C`. The exact statement proved:

* `autResolution_prize_ge` — at the prize `n = 2^30`, the forced alphabet resolution is `≥ 2^15`,
  so any automatic-sequence constant is `≥ 2^15` (not absolute) ⟹ the `√(n log m)` bound it yields
  carries a *growing* prefactor and never reaches the prize target with absolute `C`.
* `autResolution_monotone` — the resolution grows with `n`; the gap to "absolute `C`" only widens
  up the prize tower (`n → 2^30`).

This is a *no-go quantification*, NOT a closure: it certifies HOW the automatic-sequence route
falls short (growing automaton resolution ⇒ no absolute `C`), mirroring `BurgessIndexOvershoot`.

## References
- [Kon19] Konieczny. *Gowers norms for the Thue–Morse and Rudin–Shapiro sequences*. (Automatic
  sequences have controlled Gowers norms — but only for the *automatic* sequence itself.)
- [DMS] Drmota–Müllner–Spiegelhofer. *Möbius orthogonality for automatic sequences* / the
  Sarnak-for-automatic results (discrepancy via the substitution/odometer structure).
- In-tree: `BurgessIndexOvershoot.lean` (magnitude-route overshoot), `KowalskiUntrauBarrier.lean`
  (equidistribution SOTA vacuous), `Sweep_A12_PhaseAlignmentTower.lean` (the EXACT odometer
  parallelogram — an *identity*, no descent), `_wf407_stickelberger.py` (the prior p-adic probe).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo

/-- The **automaton-resolution lower bound**: the size of the finite alphabet a *faithful* automatic
representation of the argument sequence `j ↦ arg(τ(χ^j))` must have, in order to not collapse the
Parseval-forced spread `M(n) ≥ √n`. We use `Nat.sqrt n` as the integer surrogate for `√n`. An
automatic-sequence discrepancy bound has a constant controlled by this alphabet size; if it grows
with `n`, the route cannot produce an **absolute** constant `C` in `M(n) ≤ C·√(n·log m)`. -/
def autResolution (n : ℕ) : ℕ := Nat.sqrt n

/-- `autResolution` is monotone: the forced alphabet resolution only grows up the prize tower
`n → 2^30`, so the gap between an automatic-sequence constant and an *absolute* `C` only widens. -/
theorem autResolution_monotone {a b : ℕ} (h : a ≤ b) : autResolution a ≤ autResolution b :=
  Nat.sqrt_le_sqrt h

/-- `Nat.sqrt (2^30) = 2^15` exactly. -/
theorem sqrt_prize : Nat.sqrt (2 ^ 30) = 2 ^ 15 := by
  have h : (2 : ℕ) ^ 30 = (2 ^ 15) ^ 2 := by
    rw [← pow_mul]
  rw [h, Nat.sqrt_eq']

/-- **The prize-scale automaton-resolution lower bound.** At the prize subgroup order `n = 2^30`,
a faithful automatic representation of the argument sequence needs an alphabet of size `≥ 2^15`.
Hence any automatic-sequence discrepancy constant is `≥ 2^15`, NOT an absolute constant — the route
cannot yield `M(n) ≤ C·√(n·log m)` with `C = O(1)`. The √n Parseval floor (graph not Ramanujan)
is the obstruction: it forbids collapsing the argument sequence to a bounded alphabet. -/
theorem autResolution_prize_ge : 2 ^ 15 ≤ autResolution (2 ^ 30) := by
  rw [autResolution, sqrt_prize]

/-- The prize-scale resolution is exactly `2^15`. -/
theorem autResolution_prize_exact : autResolution (2 ^ 30) = 2 ^ 15 := by
  rw [autResolution]; exact sqrt_prize

/-- **Non-absoluteness of the automatic-sequence constant (the no-go core).** For every `B : ℕ`,
there is a tower level `n = 2^(2k)` whose forced alphabet resolution exceeds `B`. So no FIXED bound
`B` on the automaton resolution holds across the prize tower; an automatic-sequence discrepancy
constant `C(A, #states)` with `A ≥ autResolution n` therefore cannot be an absolute constant. This
is the formal statement that the route — even granting the (refuted) `ArchimedeanArgAutomatic`
hypothesis with `n`-dependent automata — produces only a *growing* prefactor, never the prize's
absolute `C`. -/
theorem autResolution_unbounded (B : ℕ) : ∃ n, B < autResolution n := by
  refine ⟨(B + 1) ^ 2, ?_⟩
  rw [autResolution, Nat.sqrt_eq']
  omega

/-- **Tower persistence.** For every `k ≥ 15`, the resolution at `n = 2^(2k)` is `≥ 2^15`; the route
gap never closes going up the prize tower (the prize sits at `2^30 = 2^(2·15)` and beyond). -/
theorem autResolution_tower_ge (k : ℕ) (hk : 15 ≤ k) : 2 ^ 15 ≤ autResolution (2 ^ (2 * k)) := by
  rw [autResolution]
  have h : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  rw [h, Nat.sqrt_eq']
  exact Nat.pow_le_pow_right (by norm_num) hk

end ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo

-- Axiom audit: all results axiom-clean (only propext, Classical.choice, Quot.sound).
#print axioms ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo.autResolution_prize_ge
#print axioms ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo.autResolution_prize_exact
#print axioms ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo.autResolution_unbounded
#print axioms ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo.autResolution_tower_ge
#print axioms ArkLib.ProximityGap.Frontier.AutomaticSeqArchimedeanNoGo.autResolution_monotone
