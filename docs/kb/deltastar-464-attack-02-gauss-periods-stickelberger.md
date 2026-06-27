# Attack #02 — Gaussian periods / Stickelberger / Gross–Koblitz explicit evaluation

**Date:** 2026-06-27  **Issue:** #464 (δ* / Proximity Prize)
**Verdict:** REDUCES TO PALEY. The valuation route is structurally wrong-direction;
landed an axiom-clean brick proving exactly that.

## Target theorem (what closing this angle would prove)

`WorstCaseIncompleteSumBound`: for the smooth subgroup `μ_n ⊆ F_q*` (`n=2^μ`,
prize regime `q≈n·2^128`, `n=2^30`) and every nonzero frequency `b`,
`M = max_{b≠0} ‖η_b‖ ≲ √(n log q)` with `η_b = Σ_{x∈μ_n} e_p(b x)` the nontrivial
eigenvalue of the generalized Paley graph `Cay(F_q, μ_n)`. The prize reduces to the
hyperplane upgrade `WorstCaseIncidenceBounded` (BCHKS 1.12); this upper bound on `M`
is the necessary analytic context.

## The angle: convert Gross–Koblitz valuation data into an archimedean bound

The period `η_b ∈ ℤ[ζ_p]` is, by the completion identity
(`SubgroupGaussSumWorstCase.completion_identity`), `t·η_b = Σ_{j<t} τ(χ^{dj}, ψ_b)`
with `t=(q-1)/d`, `d=n`. The Gauss sums `τ(χ)` are evaluated p-adically by
**Gross–Koblitz**: `τ(χ) = -π^{s(a)} · ∏ Γ_p(...)`, where `s(a)` is the sum of base-p
digits, pinning `v_p(τ(χ)) = s(a)/(p-1)`. **Stickelberger** packages the prime-factor
valuations of `(τ)` as the Stickelberger element `θ = Σ (a/(q-1)) σ_a^{-1}`.

The hope: the valuation data + the period polynomial's Mahler measure / house +
the `A4CyclotomicGaloisAntipodal` functional equation (`e₂(S)=0 ⟹ σ(P(ζ))=±P(ζ)`)
might bound the archimedean `|η_b|`.

## Proof attempt and where it dies

**Step 1 (the archimedean fact about a single Gauss sum is already maximal).**
`‖τ(χ,ψ)‖ = √q` *exactly* for every nontrivial `χ`
(`SubgroupGaussSumWorstCase.norm_gaussSum_eq_sqrt`, proven in-tree, no Weil). The
p-adic valuation `v_p(τ)=s(a)/(p-1)` is *orthogonal* information: it lives at the
finite place `p`, the magnitude lives at the archimedean place, and `‖τ‖=√q` is
constant across `χ`. **Valuation adds nothing archimedean about one Gauss sum.**

**Step 2 (the period is a SUM of t Gauss sums — phase cancellation is the whole game).**
`t·η_b = Σ_{j<t} τ(χ^{dj},ψ_b)`. Triangle inequality gives only `t·‖η_b‖ ≤ t·√q`
(the trivial `√q` anchor). To beat `√q` per-frequency we need *cancellation among the
t archimedean phases* `arg τ(χ^{dj})`. Gross–Koblitz fixes the p-adic valuation of
each term but says **nothing** about these archimedean arguments. The Stickelberger
element similarly controls only the finite-place factorization.

**Step 3 (norm / house arguments go the WRONG way).** The only archimedean conclusion
the multiplicative/algebraic side actually yields is a *lower* bound on the house.
`η_b` is an algebraic integer; the product of its `(q-1)/n` Galois conjugates is a
nonzero rational integer, so the geometric mean of conjugate magnitudes is `≥ 1`,
hence `house(η) ≥ 1`. Numerically (probe), the geometric mean / norm route gives
`house ≥ geomean`, a strict lower bound (e.g. `p=17,n=8`: house 2.562, geomean 2.000;
`p=97,n=32`: house 6.207, geomean 4.291). **The valuation/norm route bounds the house
from BELOW; the prize needs it from ABOVE.**

## The landed axiom-clean brick (the wrong-direction lemma, made precise)

`Frontier/_Attack02GaussPeriodHouse.lean`,
`exists_nonzero_house_lower` (axioms: `propext, Classical.choice, Quot.sound`):

> For any primitive `ψ`, any frequency set `G` with `0 < |G| < q`, there is a NONZERO
> `b` with `‖η_b‖² ≥ |G|·(q-|G|)/(q-1)`.

Proof: the second moment `Σ_b ‖η_b‖² = q·|G|` (in-tree
`subgroup_gaussSum_secondMoment`), minus the `b=0` term `‖η_0‖²=|G|²`, leaves mass
`|G|(q-|G|)` on the `q-1` nonzero frequencies; max ≥ average gives the bound. In the
prize regime `|G|=n≪q`, this is `M ≥ √(n·(1-n/q)/(1-1/q)) ≈ √n` — the Parseval house
*lower* bound. This is the strongest archimedean statement the multiplicative side
(Gauss-sum norm + orthogonality + valuation) can reach, and it is the wrong direction.

## Adversarial self-refutation

Could the **A4 functional equation** `σ(P(ζ))=±P(ζ)` (under `e₂(S)=0`) supply an
archimedean upper bound? No: it is a *sign* relation among conjugates, an algebraic
identity at the archimedean places jointly. It constrains the *phases of conjugates
relative to each other*, not the absolute magnitude — and it holds only on the
measure-zero `e₂=0` locus, not at the prize subgroup. Could the period polynomial's
**Mahler measure / house** (memory `issue444-...-house-reframe`) cross? The Mahler
measure equals the product over conjugates of `max(1,|·|)` = a multiplicative (Norm-
type) quantity; via the tropical/(max,+)=log-Mahler engine, sub-unit conjugates absorb
the Norm so the finite places give **no** max bound. That memory note already
identifies the house reframe as reducing only via the engine to bounded-height/Lehmer
for the Gaussian-period family — i.e. it **relocates** the wall, does not escape it.

So the angle survives adversarial refutation only as a clean obstruction: every
sub-route (valuation / norm / Mahler / Galois-sign) is multiplicative and bounds the
house from below.

## The exact lever / the wall

The single missing ingredient is an **archimedean phase-cancellation** statement among
the `t` arguments `arg τ(χ^{dj}, ψ_b)` — equivalently `Σ_b‖η_b‖^{2r} ≤ Wick` (DC-
subtracted) at depth `r≈log q`, equivalently BCHKS 1.12. Gross–Koblitz/Stickelberger
operate at the finite place `p` and are provably blind to it (Step 1). This is the
same Paley/BGK wall ~60 prior sessions hit; the contribution here is the precise
*directional* obstruction: the entire algebraic/valuation toolkit produces house
**lower** bounds, never the upper bound the prize requires.

## Honest verdict

- proofStatus: **reduces-to-paley**.
- The archimedean phase is genuinely untouched by p-adic valuation data; confirmed
  both by the in-tree `‖τ‖=√q` constant and by the probe showing norm/geomean is a
  lower bound on the house.
- Landed brick `exists_nonzero_house_lower` is a real, axiom-clean *lower*-bound result
  (Parseval house floor `M ≳ √n`) — useful as the documented wrong-direction witness,
  NOT a step toward the upper bound.
- Does NOT bypass Paley.
