/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-HJ1)
-/
import Mathlib

/-!
# Lane J1 (#444): the subspace theorem / S-unit / Conway–Jones / Dvornicich–Zannier route

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** Lane J1 asks whether the
Diophantine machinery that bounds the **number** of vanishing relations — Schmidt's subspace
theorem, the Evertse–Schlickewei–Schmidt (ESS) bound for `S`-unit / unit equations, the
Conway–Jones (1976) and Dvornicich–Zannier (2002) classifications of (modular) vanishing sums of
roots of unity — supplies a genuinely *non-second-order* handle on the prize sup-norm

  `M(n) = max_{b ∈ 𝔽_p^*} |η_b|`,  `η_b = Σ_{x∈μ_n} e_p(b x)`,  `μ_n = order-n=2^μ subgroup`,

at the prize regime `n = 2^30`, `p = n^β`, `β = 4`, `p ≡ 1 (mod n)`.

## The objects, and the precise literature (lane research, cited)

The energy / wraparound route bottoms out (in-tree: the char-`p`-transfer reduction chain) at the
count of **genuine char-`p` vanishing relations**

  `W_r = #{ short ±1 signed sums of n-th roots of unity that are ≡ 0 (mod p) but ≠ 0 over ℤ[ζ_n] }`,

the *"Mann's theorem mod P"* object. The S-unit machinery addresses exactly such relation counts:

* **Mann (1965) / Conway–Jones (1976, Acta Arith. 30) / Lam–Leung (2000, J. Algebra 224):**
  over ℂ, a vanishing sum of `N` `m`-th roots of unity has `N ∈ ℕ⟨prime factors of m⟩`; a *minimal*
  vanishing sum forces (squarefree) order with `Ψ(m) := 2 + Σ_{prime p∣m}(p−2) ≤ k`. For
  `m = 2^μ` the only squarefree order is `2`, `Ψ(2)=2`, so **every** char-0 vanishing 2-power sum is
  a ℤ-combination of antipodal pairs `ζ^a + ζ^{a+n/2} = 0` (this is Mann for 2-powers — char-0 done).
* **Dvornicich–Zannier (Archiv der Math. 79 (2002) 104–108), "Sums of roots of unity vanishing
  modulo a prime":** for `gcd(n,ℓ)=1` the congruence `Σ a_i ζ_i ≡ 0 (mod ℓ)` obeys the **same
  Conway–Jones inequality** as the char-0 case, with the structure theorem: an irreducible relation
  forces a root `ζ_N` of bounded order `N` with `Σ_{p∣N}(\tfrac{p−1}{\gcd(p−1,d)}−1) ≤ k−2`. This
  constrains the **order `N` of roots appearing**; it gives **no quantitative length lower bound**
  `k ≥ c·log p`, and is **independent of `ℓ`** (so it cannot see the `p`-scale at all).
* **Evertse–Schlickewei–Schmidt (Annals 155 (2002) 807–836):** the number of **non-degenerate**
  solutions of `a_1 x_1 + … + a_k x_k = 1` with `x` in a rank-`r` multiplicative group is
  `≤ exp((6k)^{3k}(r+1))`; for roots of unity (`r=0`, Evertse 1999) `≤ (k+1)^{3(k+1)^2}`. **It is a
  theorem of characteristic 0** ("Let `K` be a field of characteristic 0"), counts only
  *non-degenerate* relation TYPES (no proper subsum vanishing), and the bound is *super-exponential
  in `k`* with a known lower bound `≥ k!` (e.g. `1+ζ+…+ζ^{p−1}=0`).

## The verdict: REDUCES-TO-FENCE F9 (supply-side count cap) + F11/F1, VACUOUS at the prize

Three independent, decisive failures — the first is the machine-checked arithmetic content below.

### (1) Even when ESS applies, its COUNT is vacuous at prize depth `k ≈ log p` (the F9 cap).
The moment / supply-side route would use a relation-type count `≤ A(k)` at half-length `r`,
`k = 2r`, optimized at `r ≈ ln q ≈ 172` (prize). The ESS count `A(k) = (k+1)^{3(k+1)^2}` has
`log₂ A(2r) ≥ 3(2r)² = 12 r²` — *super-quadratic in `r`*, whereas the supply-side budget that a
useful union bound can spend is `log₂ q ≈ β·μ` = **linear in `r`** at the optimal depth (`r ≈ log q`).
So `A(k)` overshoots the entire field `𝔽_p` by an astronomical margin and tightens nothing: this is
exactly fence **F9** (effective-Chebotarev / supply-side union cap, MAXNORM `Θ(n)` ≫ band-floor
`Θ(log n)`), now restated for the S-unit count. We prove `12 r² ≤ log₂ A(2r)` below.

### (2) ESS is characteristic 0; the prize gap is the genuinely-char-`p` (`≠0` over ℤ[ζ]) relations.
ESS / Conway–Jones / Lam–Leung count char-0 relation types — for `μ_n` 2-power these are precisely
the antipodal/Mann pairings, i.e. the `(2r−1)‼` Wick matchings (fence **F1/F12**, the energy is
conjugate to the wall and the bounded-`K` Wick transfer is DEAD at β=4). The prize defect lives in
`W_r` = the char-`p`-only relations, which a char-0 count provably does **not** see.

### (3) Dvornicich–Zannier is `ℓ`-independent — it cannot reach the `√log` excess (fence F0/F11).
DZ transfers the CJ classification to the modular case but is **independent of `ℓ`**; it only bounds
the *order* of roots in an irreducible relation, supplying no rate in `p`. Exact-int probes
(`probe_wfH_J1{b,c}_*`): at prize-shaped `(n,p)`, `n∈{8,32,64}`, `p≈n⁴`, **no genuine char-`p`
`±1`-subset relation of length `≤ 5–6` exists** (the short lengths are 2-power-norm-protected) — but
this is *consistent with both* the floor and DZ, and DZ furnishes no quantitative growth law
`L*(n,p) ≥ c·log p`. So the lane is `√q`-completion-blind exactly as fence **F0** (a count whose only
input is the relation combinatorics is invisible to the `b`-phase rare-event that separates the worst
`b` from Johnson) and **F11** (the count is the conjugate-norm `#{c : p ∣ N(c)}` synonym).

## Scope (honesty contract)

A **method-boundary verdict**, NOT a prize closure and NOT a refutation of the floor. The floor
`M(n) ≤ C√(n·log(p/n))` stays OPEN, at the BGK/Paley wall. This file machine-checks failure (1) — the
ESS count's super-quadratic-vs-linear overshoot — and exports the verdict as a single implication.

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`.
Issue #444 (lane J1). Probes: `scripts/probes/probe_wfH_J1{,b,c}_*` (exact integer).
-/

open Finset

namespace ProximityGap.Frontier.SubspaceSUnitVacuous

/-- **The Evertse–Schlickewei–Schmidt / Evertse-1999 count exponent.**

For a relation of length `k` among roots of unity (rank `r = 0`), the number of non-degenerate
solutions is `≤ (k+1)^{3(k+1)^2}`; its base-2 log is `essLogCount k = 3(k+1)^2 · log₂(k+1)`. We work
with the integer *exponent* `essExp k = 3·(k+1)^2` (the polynomial degree-in-`k` of the count's log),
which already carries the decisive super-quadratic growth. -/
def essExp (k : ℕ) : ℕ := 3 * (k + 1) ^ 2

/-- **(1) The ESS count is super-quadratic in the relation half-length `r` (`k = 2r`).**

`essExp (2r) = 3·(2r+1)^2 ≥ 12·r²`. The count's log-exponent grows at least *quadratically* in the
relation half-length `r`. Contrast the supply-side budget a useful union bound can spend at the
moment method's optimal depth `r ≈ log q`: that budget is `log₂ q`, which is *linear* in `r`. Hence
the ESS count overshoots `𝔽_p` super-polynomially and supplies no constraint — fence F9. -/
theorem essExp_two_mul_ge_quadratic (r : ℕ) : 12 * r ^ 2 ≤ essExp (2 * r) := by
  unfold essExp
  have h : (2 * r + 1) ^ 2 = 4 * r ^ 2 + 4 * r + 1 := by ring
  calc 12 * r ^ 2 ≤ 3 * (4 * r ^ 2 + 4 * r + 1) := by nlinarith [Nat.zero_le r, sq_nonneg r]
    _ = 3 * (2 * r + 1) ^ 2 := by rw [h]

/-- **(1′) Super-quadratic strictly dominates any linear supply budget past a finite depth.**

For every linear supply-side budget `B·r + C` (the union-bound spend at depth `r`, with `B,C` the
prime-scale constants `log₂ q ≈ β·μ`), there is a depth `R` beyond which the ESS count exponent
exceeds the budget at *every* `r ≥ R`. So no choice of optimal depth `r ≈ log q` lets the ESS count
beat the trivial total: the count is vacuous as a supply cap. (Concretely `R = B + C + 1` works.) -/
theorem essExp_eventually_dominates_linear (B C : ℕ) :
    ∃ R, ∀ r, R ≤ r → B * r + C < essExp (2 * r) := by
  refine ⟨B + C + 1, fun r hr => ?_⟩
  have hquad : 12 * r ^ 2 ≤ essExp (2 * r) := essExp_two_mul_ge_quadratic r
  have hrpos : B + C + 1 ≤ r := hr
  -- B*r + C < 12 r^2 for r ≥ B+C+1, since r^2 ≥ (B+C+1)·r ≥ B·r + r > B·r + C.
  have hr1 : 1 ≤ r := le_trans (Nat.le_add_left 1 (B + C)) hrpos
  have key : B * r + C < 12 * r ^ 2 := by nlinarith [hrpos, hr1, sq_nonneg r, Nat.zero_le r]
  exact lt_of_lt_of_le key hquad

/-- **The lane verdict as a single implication (fence F9 form).**

Suppose — toward the S-unit route — that one tried to certify the prize floor by bounding the worst
`b` via a *union over relation types* whose count is the ESS bound at half-length `r`, spending a
linear supply budget `B·r + C` (`B,C =` prime-scale `log₂ q` constants). Then at the moment method's
optimal depth (`r ≥ R`) the ESS relation-type count strictly exceeds the budget, so the union bound
is **looser than trivial** — it cannot localize the worst `b`. Contrapositive: the S-unit count
supplies no nontrivial supply-side cap at prize depth. (This is the F9 wall restated; it does NOT
touch the genuinely-char-`p` defect `W_r`, failure (2)/(3) above, which is the actual open core.) -/
theorem subspace_sunit_route_no_supply_gain (B C : ℕ) :
    ∃ R, ∀ r, R ≤ r → ¬ (essExp (2 * r) ≤ B * r + C) := by
  obtain ⟨R, hR⟩ := essExp_eventually_dominates_linear B C
  exact ⟨R, fun r hr => not_le.mpr (hR r hr)⟩

end ProximityGap.Frontier.SubspaceSUnitVacuous

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ProximityGap.Frontier.SubspaceSUnitVacuous.essExp_two_mul_ge_quadratic
#print axioms ProximityGap.Frontier.SubspaceSUnitVacuous.essExp_eventually_dominates_linear
#print axioms ProximityGap.Frontier.SubspaceSUnitVacuous.subspace_sunit_route_no_supply_gain
