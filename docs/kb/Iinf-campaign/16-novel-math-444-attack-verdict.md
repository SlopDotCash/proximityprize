# Highly-novel-math attack on the prize / M(n) — all 7 reduce, with a proof of WHY (wf_5576da1e, 2026-06-16)

> **Scope correction (2026-10-28 audit, T48; cross T87/T104).** This verdict upgrades a finite search
> and an endpoint identity into impossibility claims that are not established.
> - **No subject is ruled out.** A modulus/valuation calculation does not prove that entire subjects
>   (algebraic, cohomological, SOS or Gowers methods) cannot use phases. The "two-column
>   orthogonality theorem" is a heuristic description, not a theorem excluding those methods.
> - **These are different objects.** Spur counts, total moments `E_r`, Fourier maxima `M(n)` and MCA
>   codeword geometry remain distinct, linked only by conditional bridges. For example
>   "`Spur_r(p)` literally equals `E_r`" is a finite numerical match, and "the two-sided prize ⟺ M(n)
>   equivalence" is not established.
> - **N6 stays open.** Curve-decodability (N6) is, as the note itself says, a genuinely distinct
>   object. It should remain distinct, not be ruled out by an endpoint-only identity.

Attacked the prize core with 7 frameworks NEVER tried in-tree (p-adic/Dwork, Pila-Wilkie, Deligne-Lusztig,
Gowers, SOS, two-sided-gap-hunt, motivic/Hecke), each required to be NON-reducing or admit reduction, 3-lens
adversarially verified. **Verdict: all 7 reduce to M(n)/second-order; no non-reducing route, no surviving
gap in the two-sided prize⟺M(n) equivalence.** But the sweep PROVED why, and surfaced one genuinely-different
object + one actionable different direction.

## Per-framework (all machine-grounded)
| framework | verdict | the reduction (proven/verified) |
|---|---|---|
| **N1 p-adic / Dwork / rigid cohomology** | reduces-to-M(n) | **Two-column orthogonality theorem** (new, clean): Frobenius eigenvalues split into an *archimedean* column (all `|τ(χ_j)|=√p` — the ONLY column bounding `M(n)`) and a *p-adic* column (Stickelberger valuations — the ONLY column Dwork/Newton-polygon computes); these are **orthogonal**. So cohomology is *structurally blind* to the L∞ archimedean sup. Verified `η_b=(1/m)·DFT(τ(χ_j))` to err 1e-13 ⇒ L∞ = moments = 2nd-order. |
| **N2 Pila-Wilkie / determinant method** | reduces-to-M(n) | `Spur_r(p)` **literally equals** `E_r` (verified to the digit: 16/3856/986896 at n=16,p=17). "Counting solutions" and "computing the moment" are the *same operation*. The constraint is one `F_p`-linear form (codim-1 *algebraic* subspace) — no transcendental part, PW vacuous; height filter prunes nothing. |
| **N3 Deligne-Lusztig** | reduces-to-M(n) | `GL_1` abelian, all degrees 1 — produces only `|g|=√p` and the Plancherel 2nd moment `(p−n)/m` = the `√n` floor. Rep-theoretic invariants are b-blind. |
| **N4 Gowers norms** | reduces-to-M(n) | `‖f‖_{U^2}^4 = Σ|f̂|^4` = additive energy = Johnson (tightest sup bound by Gowers monotonicity); the genuine degree-2 structure it finds is **exactly `2·M(n/2)`** — recurses to the same wall on `μ_{n/2}`. |
| **N5 SOS / Lasserre** | reduces-to-M(n) | non-moment certificate needs degree `≥(p−1)/2` (Fejér-Riesz half-bandwidth); every tractable degree IS the deep-moment polynomial = M(n). |
| **N6 curve-decodability / coset-saturation** | reduces — but is the genuinely-different object (see below) | the only non-moment object; for the PRIZE code `μ_n` RS it is INERT (proven). |
| **N7 motivic / Hecke / Jacobi-sum** | reduces-to-M(n) | per-character `√p` is **PROVEN** (CM/Weil/Ramanujan-Petersson) — but consumed by the `1/m` normalization, leaving prize ⟺ a dual `m`-character free-phase sup = the same open BGK wall. |

## The two genuine outputs
### (1) A PROOF of why every algebraic/cohomological/rep-theoretic method must reduce
The prize value sits in the **narrow gap between two things the algebraic side computes**: the `√p` triangle
bound (too big — `≈2^68` at prize) and the 0-dimensional trivial bound (too small — `n`). **All cancellation
lives in the PHASES `arg τ(χ_j)`, which the p-adic / cohomological / rep-theoretic side is structurally
incapable of seeing** (it computes moduli `√p` and valuations, never archimedean phases). Phase cancellation
`= Σ_b|η_b|^{2r} = E_r` = the second-order object the meta-theorem caps at Johnson. This is the sharpest
statement yet of why the 100-avenue / novel sweep all collapse — it is not luck, it is a structural theorem.

### (2) The ONE genuinely-different object — and the only non-vacuous escape (a different direction)
**N6 curve-decodability is the unique object in the entire sweep that is NOT a disguised 2nd-order moment**
(b-sensitive + archimedean-deterministic + genuinely-L∞ — it provably *sidesteps* the meta-theorem). For
codes with **strong subspace design** (FRS / multiplicity / GG25 Thm 3.3/4.7) it genuinely gives `δ* > Johnson`
char-independently — the unique known beyond-Johnson mechanism, formalized in-tree
(`GG25MCAFromCurveDecodability.lean`, `SubspaceDesignFullVanish.lean`). **But it is INERT for the prize μ_n RS
code, PROVEN:** `RadiusOneExact.epsMCA_one_eq_choose_div` (axiom-clean) forces `B(δ)=I(δ)` = the M(n) object at
the endpoint (close points on a μ_n line have distinct, non-shared agreement sets; per-triple collinearity
needs `p > (6n)^{n/2}` ≫ prize). **So the only non-vacuous escape anywhere is to CHANGE THE CODE — substitute a
subspace-design structure into the smooth-domain RS setting. That is a code-DESIGN question, not an M(n)
question** — and it is the single genuinely-different research direction the sweep surfaced.

## Verdict on "novel math that won't reduce to the same value"
For the PRIZE code, **no such math exists, and now provably so**: (a) the two-sided `prize⟺M(n)` equivalence is
airtight for μ_n RS (proven `RadiusOneExact` + n=8 q-independence), and (b) the only non-reducing object
(curve-decodability) is inert for μ_n RS (proven) and lives for *other* codes. Every algebraic/cohomological
method reduces because the cancellation is purely archimedean phase, invisible to them (the two-column
theorem). The single live open target is unchanged and unchangeable without new analytic NT: **does a short
(≤ 2 ln q-term) ±1-relation of `2^μ`-th roots of unity vanish mod the prize prime?** (= `Spur_r` = `Ξ_k` =
the char-p Lam-Leung transfer = BGK). Proven for `n ≲ 40`; OPEN at `n=2^30`.

Source: wf_5576da1e (8 agents). Still pending: the standard-proof workflow (wllo1hg5o) hunting a GRH /
log-free-zero-density CONDITIONAL close — the one path that could yield a real (conditional) result.
Related: docs 13,14,15; issue #444 §0.0,§2. Files: RadiusOneExact.lean, GG25MCAFromCurveDecodability.lean,
_wf5M2/_wf5M4 (N1), _DyadicJacobiCocycleNonContraction.lean (N7).
