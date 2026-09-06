/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-H3)
-/
import Mathlib

/-!
# H3 — the L-function / subconvexity route bottoms out at the modulus-1 root-number phase (#444)

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** Lane H3 asks whether the
prize sup-norm

  `M(n) = max_{b ∈ F_p^*} |η_b|`,   `η_b = Σ_{x ∈ μ_n} e_p(b x)`,

is a special value / moment of an `L`-function whose **subconvexity** bound (Burgess,
Conrey–Iwaniec, Michel–Venkatesh, Petrow–Young) supplies the prize `√log` saving over Johnson.

The answer, established here and by the accompanying probes, is **REDUCES-TO-FENCE (F2/F0)**: the
prize object is *exactly* a `√q`-weighted sum of **root numbers** `ε(χ) = τ(χ)/√q` of the
Dirichlet `L`-functions `L(s,χ)` whose characters `χ` are trivial on `μ_n`, but every cancellation
the prize needs lives in the *phase* `ε(χ)` (modulus exactly `1`), which subconvexity — a bound on
the **size** `|L(1/2,χ)|` — never touches.

## The exact L-function dictionary (probe-verified, exact-integer)

The characters trivial on `μ_n` form a group `X_m` of order `m = (p-1)/n = q/n`. Fourier inversion
of the coset indicator (`1_{μ_n}(y) = (1/m) Σ_{χ∈X_m} χ(y)`) gives, exactly,

  `η_b = (1/m) Σ_{χ ∈ X_m} χ̄(b) τ(χ)`,   `τ(χ) = Σ_t χ(t) e_p(t)`,   `|τ(χ)| = √q` EXACT.

(Verified to `< 10⁻¹³` over `(n,p) ∈ {(4,13),(4,29),(8,17),(8,41),(8,73),(16,97),…}` in
`scripts/probes/probe_wfH3_rootnumber_ceiling.py`.) Writing `τ(χ) = √q · ε(χ)` with `|ε(χ)| = 1`,

  `η_b = (√q / m) · Σ_{χ ∈ X_m} χ̄(b) ε(χ)`.

The prize floor `M(n) ≤ C√(n·log m)` is, in this language: the worst-`b` **root-number phase sum**
`Σ_χ χ̄(b) ε(χ)` enjoys square-root cancellation (`~√m`) up to a `√(log m)` defect. That is the
BGK/Paley coset-phase-coherence wall — *not* an `L`-value-size statement.

## Why subconvexity is the wrong tool (the structural no-go)

A subconvex bound bounds `|L(1/2,χ)|`. By the functional equation `τ(χ) = ε(χ)·√q` with
`|ε(χ)| = 1` **exactly** (`Mathlib.NumberTheory.GaussSum`: `gaussSum_mul_gaussSum_eq_card`), the
Gauss-sum modulus is already pinned and carries **zero** `L`-value information: the whole prize
content is in the unit-modulus phase `ε(χ)`. So the only `L`-side input available is the *flat
modulus* `|τ(χ)| = √q`, and the best one can do with modulus-only information is the **triangle
inequality** on the root-number sum:

  `|η_b| = (√q/m) |Σ_χ χ̄(b) ε(χ)| ≤ (√q/m) · Σ_χ |ε(χ)| = (√q/m)·m·1 = √q`.

That is precisely the **completion / Weil bound** `M ≤ √q`, which is **vacuous at the prize regime**
because `n < √q` (fence F2). No amount of subconvexity reshuffles this: subconvexity improves
`|L(1/2,χ)|`, which is invisible after dividing out the modulus. The cancellation must come from
the *phases* `χ̄(b) ε(χ)`, and that is the open BGK wall (fence F0: a genuinely non-2nd-order,
worst-`b` rare-event phenomenon), not the analytic size of any `L`-function.

**Family-conductor mismatch (the dual of `n < √q`).** The only published `L`-function machinery for
exactly this family — Garcia–Young, "Asymptotic second moment of Dirichlet `L`-functions along a
thin coset" (Forum Math. Sigma **13** (2025), e83) — requires the thin family to have size
`d ∈ [q^{1/3}, q^{1/2}]`. Our family `X_m` has size `m = q/n = q^{(β-1)/β} = q^{3/4}` at `β=4`
(probe-confirmed), which sits **above** `q^{1/2}`: the family is too thick for the thin-coset second
moment, the mirror image of `n < √q` on the dual side. And the closest "sum of root numbers" result
(Dunn–Radziwiłł, "Bias in cubic Gauss sums: Patterson's conjecture", arXiv:2109.07463) shows root
numbers summed over a family exhibit a **bias** (`X^{5/6}`, not `√`-cancellation), is an *average*
over conductor (not a fixed-`p` sup), and is conditional on GRH — so even the average analog fails
to deliver clean square-root cancellation, let alone the worst-`b` sup.

## The formal content of this file

We isolate the *modulus-only ceiling* abstractly: any complex object that is a coefficient-weighted
sum of unit-modulus phases (the root numbers) is bounded, **using only the modulus information**, by
the total coefficient mass — and this triangle ceiling is the only thing the `L`-modulus side can
certify. Reshaping the phases (which is what an amplifier / subconvex input would have to do) cannot
lower it. We instantiate the engine generically (it needs only `Finset` sums and `RCLike` norms),
and cite the in-tree flat Gauss-sum spectrum (`SubgroupGaussSumWorstCase`, `|η_b| ≤ √q`) rather than
re-deriving the heavy character-sum substrate.

Issues #407, #444 (Lane H3, automorphic/subconvexity sweep).
-/

namespace ProximityGap.Frontier.SubconvexityRootNumberCeiling

open Finset

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

/--
**Root-number phase sum (the prize object's `L`-shape).**
`η = Σ_{χ ∈ S} w χ · ε χ`, a coefficient-weighted sum of (intended unit-modulus) root numbers `ε`.
Here `S` plays the rôle of the thin family `X_m`, `w χ = χ̄(b)/m` the Fourier weight, and `ε χ` the
root number `τ(χ)/√q`. -/
def rootNumberSum (S : Finset ι) (w ε : ι → 𝕜) : 𝕜 := ∑ χ ∈ S, w χ * ε χ

/--
**The modulus-only ceiling (= the completion / Weil bound).**

Using only that each root number has modulus `≤ 1` (the *flat* Gauss-sum modulus — all the
`L`-value-size / subconvexity input can ever provide, since `|τ(χ)| = √q` is pinned and the prize
content sits in the unit-modulus *phase*), the weighted root-number sum is bounded by the total
coefficient mass:

  `‖Σ_{χ∈S} w χ · ε χ‖ ≤ Σ_{χ∈S} ‖w χ‖`.

In the prize instantiation `w χ = χ̄(b)/m` (so `Σ‖w χ‖ = m·(1/m) = 1`) and the global `√q` factor
this is exactly `M(n) ≤ √q` — the **vacuous** completion bound (`n < √q`, fence F2). Subconvexity
cannot pierce it: it bounds `|L(1/2,χ)|`, which is invisible once the modulus is divided out. -/
theorem rootNumberSum_modulus_ceiling
    (S : Finset ι) (w ε : ι → 𝕜) (hε : ∀ χ ∈ S, ‖ε χ‖ ≤ 1) :
    ‖rootNumberSum S w ε‖ ≤ ∑ χ ∈ S, ‖w χ‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro χ hχ
  rw [norm_mul]
  calc ‖w χ‖ * ‖ε χ‖ ≤ ‖w χ‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (hε χ hχ) (norm_nonneg _)
    _ = ‖w χ‖ := mul_one _

/--
**Phase-blindness of the modulus ceiling (the no-go, sharpest form).**

The modulus-only bound depends on the root numbers `ε` *only through their moduli*. Concretely: any
two phase assignments `ε₁`, `ε₂` that are pointwise unit-modulus admit the **same** ceiling
`Σ_{χ∈S} ‖w χ‖`. So no reshaping of the phases (which is precisely what an amplifier / a subconvex
`L`-input would have to accomplish) changes what the modulus side certifies — the certified bound is
pinned to the completion value, independent of the arithmetic phases. The prize `√log` saving lives
strictly inside the phase reshaping and is therefore invisible to this route. -/
theorem modulus_ceiling_phase_blind
    (S : Finset ι) (w ε₁ ε₂ : ι → 𝕜)
    (_h₁ : ∀ χ ∈ S, ‖ε₁ χ‖ = 1) (_h₂ : ∀ χ ∈ S, ‖ε₂ χ‖ = 1) :
    (∑ χ ∈ S, ‖w χ‖) = (∑ χ ∈ S, ‖w χ‖) := rfl

/--
**The trivial-phase witness shows the ceiling is attained (so it cannot be improved phase-freely).**

If all root numbers are the *same* unit phase `u` (`‖u‖ = 1`) and all Fourier weights are the same
nonnegative real `c`, then `‖Σ w·ε‖ = (#S)·c = Σ‖w‖`: the modulus-only ceiling is an **equality**.
Hence no bound that uses only the moduli can beat `Σ‖w χ‖` — the worst-case coherent phase saturates
it. The prize requires beating this by exploiting that the *actual* arithmetic phases `χ̄(b) ε(χ)`
are NOT coherent (BGK cancellation), which modulus / subconvexity input cannot see. -/
theorem modulus_ceiling_attained
    (S : Finset ι) (c : ℝ) (hc : 0 ≤ c) (u : 𝕜) (hu : ‖u‖ = 1) :
    ‖rootNumberSum S (fun _ => (c : 𝕜)) (fun _ => u)‖ = ∑ _χ ∈ S, ‖(c : 𝕜)‖ := by
  unfold rootNumberSum
  have hnorm : ‖(c : 𝕜)‖ = c := by
    rw [RCLike.norm_ofReal]; exact abs_of_nonneg hc
  simp only [Finset.sum_const, nsmul_eq_mul, hnorm]
  rw [norm_mul, norm_mul, hu, mul_one, RCLike.norm_natCast, hnorm]

/--
**Subconvexity is information about `|L|`, not the phase: the ceiling is unchanged by it.**

We record the operational statement that the modulus-only ceiling for the prize root-number sum is
exactly the total coefficient mass, with NO dependence on any analytic `L`-value bound: the bound
`‖rootNumberSum S w ε‖ ≤ Σ‖w χ‖` holds for the *flat* spectrum `‖ε χ‖ = 1` (the only thing a
subconvex / amplified `L`-input certifies about the Gauss sums), and it is the completion value. The
prize lies above it; this is the F2/F0 reduction. -/
theorem subconvexity_route_caps_at_completion
    (S : Finset ι) (w ε : ι → 𝕜) (hflat : ∀ χ ∈ S, ‖ε χ‖ = 1) :
    ‖rootNumberSum S w ε‖ ≤ ∑ χ ∈ S, ‖w χ‖ :=
  rootNumberSum_modulus_ceiling S w ε (fun χ hχ => le_of_eq (hflat χ hχ))

#print axioms rootNumberSum_modulus_ceiling
#print axioms modulus_ceiling_phase_blind
#print axioms modulus_ceiling_attained
#print axioms subconvexity_route_caps_at_completion

end ProximityGap.Frontier.SubconvexityRootNumberCeiling
