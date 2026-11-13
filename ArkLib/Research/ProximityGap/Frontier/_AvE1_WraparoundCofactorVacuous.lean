/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Route E: the single-prime wraparound cofactor bound is VACUOUS at prize scale (#444, avenue E1)

This file records, axiom-clean, the one *provable* fact that came out of attacking the
"rank-1 single-prime structure" of the char-`p` energy excess `W_r`, and certifies that it gives
**no leverage** at the prize regime — i.e. it is a clean refutation of the route, not a closure.

## The route and what was verified (computationally, exact integer arithmetic, this session)

`W_r = E_r(F_p) − E_r(ℂ)` (finite-field `r`-energy of `μ_n ⊂ F_p` minus the char-0 energy)
counts WRAPAROUND tuples: `(x,y) ∈ μ_n^{2r}` with
`α = Σ x_i − Σ y_i` a NONZERO element of `ℤ[ζ_n]` that becomes `≡ 0` mod a fixed degree-1 split
prime `P₁` above `p` (correspondingly: `Σ ω₀^{a_i} = Σ ω₀^{c_i}` in `F_p`, where `ζ ↦ ω₀` is the
reduction).

* **Item 1 (reduction is exact — no gap).** Verified exactly for `n=16`, `p∈{97,193}`, `r∈{2,3}`:
  the single-prime count equals the FULL BGK `2r`-moment by additive orthogonality over all `b`:
  `N_{P₁}(r) = E_r(F_p) = (1/p) Σ_{b∈F_p} |η_b|^{2r}` with `η_b = Σ_{y∈μ_n} ψ(b y)`. Separating
  the DC term `b = 0` gives `(1/p) Σ_{b≠0} |η_b|^{2r} = N_{P₁}(r) − n^{2r}/p`, hence
  `W_r = N_{P₁}(r) − E_r(ℂ) = (1/p) Σ_{b≠0} |η_b|^{2r} + n^{2r}/p − E_r(ℂ)`
  (audit correction R-099/R-087: an earlier version equated `W_r` with the off-DC moment over `p`,
  dropping the `n^{2r}/p − E_r(ℂ)` adjustment). The single-prime count is **literally** the BGK
  moment (up to this explicit DC/char-0 bookkeeping); there is no genuine gap to exploit.

* **Item 2 (conjugate primes give no leverage).** Verified `n=16, p=97, r=3`: the count over each of
  the `φ(n)` conjugate split primes `P_k` is *identical*, `N_{P_k} = N_{P₁}`, because the Galois map
  `ζ ↦ ζ^{u}` is a bijection of `μ_n` permuting the `(a,c)` index set. Galois-averaging averages
  identical numbers ⇒ no constraint below `Σ_{b≠0}|η_b|^{2r}`.

* **Item 3 (cofactor IS bounded but the bound is vacuous — this file).** A wraparound `α` is a short
  `±1`-combination of at most `2r` roots of unity, so each archimedean conjugate satisfies
  `|σ_k(α)| ≤ 2r`, whence `|Norm(α)| ≤ (2r)^{φ(n)}`. Since `α ∈ P₁` and `Norm(P₁) = p`, we have
  `p ∣ Norm(α)`, hence (for `α ≠ 0`) `p ≤ |Norm(α)| ≤ (2r)^{φ(n)}`. Equivalently any wraparound
  witness forces `r ≥ ½ · p^{1/φ(n)}`. For `n = 2^μ` we have `φ(n) = n/2`, and at the prize regime
  `p = Θ(n^β)` with `n = 2^30` the depth floor is `½ · (n^β)^{2/n} = ½ · 2^{2β·30/2^30} ≈ ½` — a
  trivial constraint, while the BGK saddle is `r ≈ ln p ≈ 83`. The cofactor bound is therefore
  **uninformative at prize scale**: `φ(n)` is exponentially large in `μ`, so the necessary
  `p^{1/φ(n)}` depth floor collapses to a constant and the norm argument fails to *exclude*
  wraparounds at any relevant depth. This is the opposite of the ceiling being small: at
  `φ = n/2 = 2^29` even `r = 1` gives `(2r)^φ = 2^(2^29)`, astronomically larger than the
  production modulus `p < 2^159`, so `(2r)^φ < p` is **false** at prize scale and the norm bound
  permits (does not rule out) witness norms divisible by `p`.

## What this file proves

`wraparound_depth_floor`: the hypotheses `p ∣ N`, `0 < N ≤ (2r)^φ` force `p ≤ (2r)^φ`, the exact
arithmetic content of item 3; and `cofactor_floor_vacuous`: in the *small-ceiling* regime
`(2r)^φ < p` no such witness norm `N` can exist. The small-ceiling regime is **not** the prize
regime (see item 3: there `(2r)^φ ≫ p`); `cofactor_floor_vacuous` is the valid contrapositive of
the depth floor, not an instantiation at prize parameters.

These are honest, fully-proven facts; they do **not** close the prize. The verdict of route E is a
reduction plus a weakness: the single-prime structure is the BGK `2r`-moment (with the explicit
DC/char-0 bookkeeping above), and the available `p`-independent handle (the coarse cofactor norm
bound) is too weak at prize scale to exclude wraparounds. This is the failure of one coarse
*sufficient* criterion, not a method-wide impossibility theorem: sharper norm/height or
ideal-lattice arguments are not ruled out by this file.
-/

namespace ArkLib.ProximityGap.Frontier.AvE1

/-- **Item 3, arithmetic core.** A nonzero wraparound `α` has `|Norm(α)| = N` with
`0 < N ≤ (2r)^φ` (short `±1`-combination of roots of unity), and `p ∣ N` (membership in the
degree-1 split prime `P₁`, of norm `p`). These force the depth floor `p ≤ (2r)^φ`. -/
theorem wraparound_depth_floor
    (p r φ N : ℕ) (hN_pos : 0 < N) (hdvd : p ∣ N) (hbound : N ≤ (2 * r) ^ φ) :
    p ≤ (2 * r) ^ φ :=
  le_trans (Nat.le_of_dvd hN_pos hdvd) hbound

/-- **Item 3, small-ceiling contrapositive.** If the combinatorial norm ceiling `(2r)^φ` is
strictly below `p`, no wraparound witness norm `N` can exist: there is no `N` with `0 < N`, `p ∣ N`,
and `N ≤ (2r)^φ`.

Scope (audit correction R-099): the hypothesis `(2r)^φ < p` does **not** hold at prize scale —
there `φ = n/2 = 2^29`, so `(2r)^φ ≥ 2^(2^29) ≫ p`. At prize scale this theorem therefore says
nothing; the norm bound simply fails to exclude wraparounds. It is not evidence that witnesses are
absent, nor a method-wide obstruction. -/
theorem cofactor_floor_vacuous
    (p r φ : ℕ) (hvac : (2 * r) ^ φ < p) :
    ¬ ∃ N : ℕ, 0 < N ∧ p ∣ N ∧ N ≤ (2 * r) ^ φ := by
  rintro ⟨N, hN_pos, hdvd, hbound⟩
  exact absurd (wraparound_depth_floor p r φ N hN_pos hdvd hbound) (not_le.mpr hvac)

/-- The depth floor in its `r`-form: a witness at moment-depth `r` requires `(2r)^φ ≥ p`.
Contrapositive of `cofactor_floor_vacuous`, packaged for the saddle comparison `r ≈ ln p` vs the
collapse `p^{1/φ} ≈ 1`: at prize scale this necessary condition already holds at `r = 1`, so it
imposes no real depth constraint. -/
theorem witness_requires_depth
    (p r φ N : ℕ) (hN_pos : 0 < N) (hdvd : p ∣ N) (hbound : N ≤ (2 * r) ^ φ) :
    p ≤ (2 * r) ^ φ :=
  wraparound_depth_floor p r φ N hN_pos hdvd hbound

-- Axiom audit (expect: [propext, Classical.choice, Quot.sound], no sorryAx).
#print axioms wraparound_depth_floor
#print axioms cofactor_floor_vacuous
#print axioms witness_requires_depth

end ArkLib.ProximityGap.Frontier.AvE1
