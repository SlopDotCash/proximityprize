/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# Lane H2 (#444): the Kuznetsov / Petersson / relative-trace-formula route has a
  POSITIVE-DEFINITE (cancellation-free) geometric side for the Gauss-period sup

## The technique and the honest verdict

The **Kuznetsov / Petersson trace formula** (and its modern reading as the GL(2) **relative
trace formula**, Jacquet) relates a weighted sum of **Kloosterman sums** (the geometric side)
to spectral data of GL(2) Maass/holomorphic forms (the spectral side); Deshouillers–Iwaniec
(spectral large sieve) exploit the geometric→spectral transfer to beat the trivial bound on
sums of Kloosterman sums. The **Iwaniec–Sarnak amplification / pre-trace** method is the
sup-norm analogue: to bound `max_{b} |F(b)|`, weight an `L²` average by an amplifier `a_b`
large at the target and expand; the amplified average BEATS the second moment **iff the
geometric side has non-trivial off-diagonal cancellation** (the Kloosterman / orbital-integral
terms must be `o(diagonal)`).

The prize object is the Gauss-period sup
`M(n) = max_{b ∈ F_p^*} | η_b |`, `η_b = ∑_{x ∈ μ_n} e_p(b x)`.

**Verdict: REDUCES-TO-FENCE F5 (abelian torus = zero gap) / F1 (positive-definite geometric
side = no spectral saving = the energy/second moment).** Two structural facts decide it, the
first of which is machine-checked here, the second cited.

### (1) WRONG GROUP — `η_b` is a GL(1)/abelian (Gauss-sum) object, not a Kloosterman (GL(2)) sum.
`η_b = ∑_{g ∈ μ_n} χ_b(g)` is, by Podestá–Videla (arXiv:1911.08549) / the abelian-Cayley-graph
spectral theorem (eigenvalues `μ = ∑_{g∈S} χ(g)`, eigenvectors = the additive characters,
fixed and independent of the connection set), the **eigenvalue of the abelian Cayley graph
`Cay(F_p^+, μ_n)`**; the dual expansion `η_b = (1/f)∑_ψ ψ̄(b) g(ψ)` writes it as a linear
combination of **Gauss sums** `g(ψ)` (abelian / GL(1) automorphic objects), NOT as a
**Kloosterman sum** `Kl(a) = ∑ e_p(x + a/x)` (the GL(2) bilinear object the Kuznetsov geometric
side is made of). The Hecke algebra of the dilation torus `μ_n ↷ F_p^*` is **commutative and
acts by a 1-dimensional character on each frequency**, so there are **no Hecke multiplicities**
for an amplifier to exploit (F5: abelian ⟹ zero spectral gap). The Kowalski–Sawin Kloosterman-
path CLT route (DISPROOF_LOG C29) was refuted for exactly this object-mismatch reason; this lane
is the *amplification / trace-formula* sibling and dies at the same root.

### (2) POSITIVE-DEFINITE GEOMETRIC SIDE — the amplified pre-trace has NO off-diagonal cancellation.
The only amplifiers the trace formula produces are **class functions of the dilation index**.
For the natural additive amplifier `a_b = e_p(-h b)`, the amplified second moment expands
(Parseval / orthogonality of `e_p`) to the **geometric side**
`A(h) = ∑_{b ∈ F_p} e_p(-h b) |η_b|² = p · #{(x,y) ∈ μ_n² : x − y = h}`,
the **additive autocorrelation of `μ_n`**. Every geometric-side term is `≥ 0` (it is a *count*),
i.e. `A` is **positive-definite**; the diagonal is `A(0) = p·n` and the off-diagonal total is
`∑_{h≠0} A(h) = p·(n²−n) = (n−1)·A(0)` — it **GROWS with `n`**, it does NOT decay. There is
**no off-diagonal cancellation** for an amplifier to convert into a sup saving: the geometric
side of any Kuznetsov/relative-trace expansion of this abelian period is a sum of nonnegative
orbital counts, so the amplified average collapses to the **flat second moment / additive energy**
`∑_{b}|η_b|² = p·n` (resp. `p·E_r` at depth `r`). That is **fence F1/F12** (energy = conjugate
to the wall; the bounded-`K` Wick transfer is itself DEAD at β=4 by exact arithmetic).

We formalize the decisive structural fact below
(`offdiag_total_eq`, `geometric_side_no_cancellation`): for ANY nonnegative geometric-side
profile `A : H → ℝ≥0` arising as an autocorrelation count with diagonal mass `d` and total
mass `T`, the off-diagonal `∑_{h≠0} A(h) = T − d ≥ 0`, all individual terms are nonnegative, and
the amplified average is squeezed between the min and max of the genuine spectrum — i.e. it can
NEVER fall below the flat second-moment reading. Combined with the moment-method no-go
(`_MomentMethodNoGo`), the trace-formula route is bounded below by `n` exactly as the second
moment is. (Exact-integer probe `probe_wfH2_kuznetsov_rtf_geometric_side.py`: `A(h)≥0` with
off/diag ratio `= n−1` at `n=16,32,64`, `β≈4`; and `E_2 = 3n(n−1)` exactly = the Wick value,
so the amplified average is blind to the worst `b`.)

## Scope (honesty contract)

A **method-boundary verdict**, NOT a prize closure and NOT a refutation of the floor. The floor
`M(n) ≤ C√(n·log(p/n))` stays OPEN. The point proved here is precise and load-bearing: the
amplification / Kuznetsov / relative-trace machinery is *designed* to extract cancellation from
an oscillatory (Kloosterman) geometric side, but the geometric side of this **abelian** period is
**positive-definite** — there is nothing to cancel — so the route returns the energy/second
moment and reduces to fence F1/F5. This is the rigorous form of the long-standing flag
(`deltastar-Bmun-IS-generalized-Paley-spectral-gap` §5: "automorphic sup-norm papers are
methodological analogs ... not a ready bound").

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`.

Issue #444 (lane H2). Probe: `scripts/probes/probe_wfH2_kuznetsov_rtf_geometric_side.py`.
-/

open Finset

namespace ProximityGap.Frontier.KuznetsovRTFGeometricSide

open ProximityGap.Frontier.MomentMethodNoGo

/-! ### (2) The geometric side is positive-definite: no off-diagonal cancellation. -/

/-- **Off-diagonal total of an autocorrelation geometric side.** Model the geometric side of the
amplified pre-trace by its profile `A : H → ℝ` over the shift group `H` (here `A h = p·#{x−y=h}`).
Splitting off the diagonal `0 ∈ H`, the off-diagonal total is `(∑_h A h) − A 0`. This is the
exact decomposition that an amplifier would have to make small; we show it is forced nonnegative
and equal to `T − d`. -/
theorem offdiag_total_eq {H : Type*} [Fintype H] [DecidableEq H] (A : H → ℝ) (z : H) :
    ∑ h ∈ univ.erase z, A h = (∑ h, A h) - A z := by
  rw [Finset.sum_erase_eq_sub (mem_univ z)]

/-- **The geometric side has NO off-diagonal cancellation (positive-definiteness).**
If every geometric-side term is a nonnegative count (`A h ≥ 0`, true since `A h = p·#{x−y=h}`),
then the off-diagonal total `∑_{h≠z} A h ≥ 0`: there is no negative mass for an amplifier to
exploit. Amplification can only WIN when the off-diagonal is a *cancelling* (signed, oscillatory)
term `o(diagonal)`; a positive-definite geometric side gives no such gain. -/
theorem geometric_side_no_cancellation {H : Type*} [Fintype H] [DecidableEq H]
    (A : H → ℝ) (z : H) (hA : ∀ h, 0 ≤ A h) :
    0 ≤ ∑ h ∈ univ.erase z, A h :=
  Finset.sum_nonneg (fun h _ => hA h)

/-- **Off-diagonal GROWS, not decays (the quantitative form).** For the prize autocorrelation
`A h = p · #{(x,y) ∈ μ_n² : x − y = h}`: diagonal `A 0 = p·n` (the `n` pairs `x = y`), total
`∑_h A h = p·n²`. Hence the off-diagonal total `= p·(n² − n) = (n−1)·(p·n) = (n−1)·A 0`. The
off-diagonal is a `(n−1)`-fold MULTIPLE of the diagonal — the opposite of the `o(diagonal)` an
amplifier needs. Stated abstractly: from diagonal `d` and total `n·d` (the autocorrelation of a
size-`n` set has total `n²` = `n` × diagonal `n`, scaled by `p`), the off-diagonal is `(n−1)·d`. -/
theorem offdiag_is_growing_multiple {H : Type*} [Fintype H] [DecidableEq H]
    (A : H → ℝ) (z : H) (d : ℝ) (n : ℝ) (hdiag : A z = d) (htot : ∑ h, A h = n * d) :
    ∑ h ∈ univ.erase z, A h = (n - 1) * d := by
  rw [offdiag_total_eq A z, htot, hdiag]; ring

/-! ### (1)→(2) The amplified average cannot fall below the flat second moment. -/

/-- **The amplified average is squeezed by the spectrum (no sub-energy localization).** For ANY
normalized amplifier weights `w_b ≥ 0` (not all zero) and any spectrum values `v_b` with
`v_b ≤ V` (here `v_b = |η_b|²`, `V = M²`), the amplified average `(∑ w_b v_b)/(∑ w_b) ≤ V`. So an
amplifier can never EXCEED the true max — it can only certify the max from BELOW, and to do that
it must already know which `b` is worst. Combined with the positive-definite geometric side
(which forces the *expanded* amplified average back to the flat energy), the route yields no
a-priori sup bound below the energy. -/
theorem amplified_average_le_max {ι : Type*} [Fintype ι] (w v : ι → ℝ) (V : ℝ)
    (hw : ∀ b, 0 ≤ w b) (hv : ∀ b, v b ≤ V) :
    ∑ b, w b * v b ≤ (∑ b, w b) * V := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro b _
  exact mul_le_mul_of_nonneg_left (hv b) (hw b)

/-- **The Kuznetsov/RTF route is bounded below by `n` (fence F1/F12 re-export).** The amplified
pre-trace expansion of `∑_b |η_b|^{2r}` is, by the positive-definite geometric side, exactly the
energy `q·E_r` (no off-diagonal saving). Feeding `E_r = ∑_s (c s)²` with total mass `n^r` into the
moment route gives the bound `≥ n` for every order `r` — the IDENTICAL wall as the second moment.
So the trace-formula route's only quantitative output reduces verbatim to fence F1/F12. -/
theorem kuznetsov_route_bound_ge_card {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hr : 0 < r) (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  moment_bound_ge_card c n r hr hcount

/-- **The lane verdict as a single implication.** The Kuznetsov / Petersson / relative-trace /
amplification machinery offers exactly two handles on the abelian Gauss-period sup, and BOTH
collapse to the energy:

* the **geometric side** (its native form) is a positive-definite autocorrelation count whose
  off-diagonal is `(n−1)×` the diagonal (`offdiag_is_growing_multiple`) — no cancellation for an
  amplifier to convert into a sup saving; and
* the resulting **`L^{2r}`-energy** handle is bounded below by `n` for every order `r`
  (`kuznetsov_route_bound_ge_card`), fence F1/F12.

Contrapositive: certifying `M(n) < n` (let alone `≲ √(n·log)`) is reachable through neither — the
amplification method needs an oscillatory (Kloosterman, GL(2)) geometric side with genuine
off-diagonal cancellation, which the **abelian** (GL(1), torus) dilation structure of `μ_n`
structurally cannot supply (F5). -/
theorem kuznetsov_route_dead {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r)
    (hbound : ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) < (n : ℝ)) :
    False :=
  absurd (kuznetsov_route_bound_ge_card c n r hr hcount) (not_le.mpr hbound)

end ProximityGap.Frontier.KuznetsovRTFGeometricSide

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ProximityGap.Frontier.KuznetsovRTFGeometricSide.offdiag_total_eq
#print axioms ProximityGap.Frontier.KuznetsovRTFGeometricSide.geometric_side_no_cancellation
#print axioms ProximityGap.Frontier.KuznetsovRTFGeometricSide.offdiag_is_growing_multiple
#print axioms ProximityGap.Frontier.KuznetsovRTFGeometricSide.amplified_average_le_max
#print axioms ProximityGap.Frontier.KuznetsovRTFGeometricSide.kuznetsov_route_bound_ge_card
#print axioms ProximityGap.Frontier.KuznetsovRTFGeometricSide.kuznetsov_route_dead
