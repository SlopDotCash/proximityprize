# δ* #466 — independent exploration cycle (2026-07-08)

Bold-exploration session (honesty contract axis A): invent new angles on the open core, test
each numerically, refute or advance. **No fabricated closure.** Outcome: four distinct novel
attempts, all axiom-clean/probe-honest, **all converge to the campaign's known open crux** —
strong independent confirmation the cartography is correct and the prize is genuinely open.

Probes: `scripts/probes/probe_r25_dyadic_doubling.py`, `..._burgess_regime.py`,
`..._wraparound_onset.py`.

## 1. Dyadic square-root doubling recursion — REFUTED (log-free form)
`μ_{2^{k+1}} → μ_{2^k}` via squaring is 2-to-1 with fibers `{±√w}`, giving an exact recursion
`η_b(μ_{2^{k+1}}) = Σ_{w∈μ_{2^k}} [e_p(b·r(w)) + e_p(−b·r(w))]`. Tested candidate telescoping
bound `D_{k+1} ≤ D_k + √(2^k)` and ceiling `D_k ≤ √(2·2^k)`: **both FAIL** in the intermediate
regime `n ~ p^{1/2}` (measured `D/√n` up to 2.3–4.0). The square-root map `r(w)` is nonlinear,
so no clean recursion survives — this is *why* the doubling structure doesn't crack it.

## 2. Correct scaling law — RECONFIRMED from scratch
Root cause of (1): the log-free normalization is wrong. In the Burgess regime `p ≈ n^4`,
`D/√n` grows (1.96, 2.67, 3.46 for n=4,8,16), but with the dossier's **`log(p/n)` factor**,
`C := M/√(n·log(p/n)) = 0.96, 1.07, 1.20` — inside the dossier's measured `[1.07,1.49]`,
hugging √2. Independent rederivation of the correct prize object `M ≤ C√(n·log(p/n))`.

## 3. Wraparound onset via the lattice 𝔭 = (p, ζ−a) — reframed to the KNOWN crux
A signed vanishing sum of distinct `μ_n` elements mod p ⟺ a short vector of the prime ideal
`𝔭 ⊂ ℤ[ζ_n]` above p (splits completely since `n | p−1`), with box-constrained coords. This
reframes the char-p obstruction as a shortest-vector question on 𝔭. It is exactly the dossier's
face 3↔4 ("do short `≤2ln q`-term ±1-relations of `2^μ`-th roots vanish mod the prize prime") —
a known equivalent, not new.

## 4. Additive-energy surplus at depth r=2 — char-0-CLEAN (no wraparound)
Measured `E(μ_n) = #{x₁+x₂=x₃+x₄}` in the Burgess regime: `E/n² = 2.25, 2.63, 2.81, 2.91,
2.95, 2.98` for `n=4…128`, converging to **3**. But `3n²` is precisely the char-0 **symmetric**-
Wick value for a set closed under negation (`−1∈μ_n`): the surplus over `2n²` is entirely the
antipodal block at sum `s=0`. So there is **no char-p wraparound surplus at r=2** — the 4th
moment is char-0-clean in the prize regime. Confirms the campaign's "every fixed-r face closes
off-BGK; the residual is the joint limit `r ≈ ln q`."

## 5. Onset scaling law — pigeonhole r* ≈ β = log_n(p)  [NEW]
Minimal moment order with char-p wraparound `W_{2r}>0`, measured (`probe_r25_onset_scaling.py`):
`β=2 → r*=2` (n=16), `β=3 → r*=4` (n=16), `β=4 → r*=4` (n=16), none for smaller n. Matches the
pigeonhole prediction `r* ≈ β` (wraparound once `n^r ≳ p`). Consequence: at the prize (β=4,
n=2^30) raw wraparound turns on at `r ≈ 4 ≪ ln q ≈ 109` — the raw moment tower is NOT char-0-clean
at the depth the prize needs. This rederives the DC-crossover (`DCEnergyEssential`): for `r>β` the
wraparound term `p·W ~ n^{2r}` **exactly cancels the DC subtraction** `n^{2r}`, so the bound is set
by the *subleading* DC-subtracted excess — which is why DC-subtraction is essential.

## 6. Moment method is TIGHT and RECOVERS the prize scale  [NEW, strongest]
`probe_r25_moment_recovers_prize.py`: `min_r S_r^{1/2r}` (S_r = Σ_{b≠0}|η_b|^{2r}) recovers the true
`max_{b≠0}|η_b|` within **1.11–1.17×**, with optimizing depth `r* ≈ ln q` — confirming the campaign's
"min over r ≈ ln q" picture is quantitatively correct. Bound value hugs `√(n·log(p/n))` with C in
the dossier's `[1.07,1.49]`.

## 7. DC-subtracted spectrum is uniformly SUB-WICK  [NEW, decisive]
`probe_r25_dc_subtracted_gaussian.py`: `R_r := S_r / [(p-1)(2r-1)!!·σ^{2r}]`, σ²=mean_{b≠0}|η_b|²,
measured **≤ 1 for every r and DECREASING** (n=8,16,32, β=4). `R_r ≤ 1` uniform ⟹ the moment method
yields `max_{b≠0}|η_b| ≤ √(n·ln q)` = **the prize bound**. So the entire prize (moment route) is the
single uniform inequality `R_r ≤ 1` (= DC-subtracted sub-Wick = `AwaySupBound`). Crux localizes by
rung: `R_2 = 0.87→0.94→0.97 → 1⁻` (PROVEN r=2 rung, vanishing margin), `R_3 = 0.66→0.82→0.91 → 1⁻`
(first OPEN rung — fresh evidence it holds, approaching 1 from below, no crossing observed). The
growing sub-Wick margin at higher r is direct evidence the floor is TRUE (δ* strictly inside window).

## 8. NEW: the pair-collision moment law  R_r = 1 − C(r,2)/n + O((r²/n)²)  [main result]
Measured `c_r := n(1−R_r)` for the dyadic subgroup at typical Burgess primes
(`probe_r25_r3rung_evidence.py`, `probe_r25_crfit.py`):

| r | C(r,2) | n=32 | n=64 | (1−R_r) trend over n=8..256 |
|---|--------|------|------|------------------------------|
| 2 | 1  | 1.009 | 1.005 | 0.127,0.063,0.031,0.016,0.008,0.004 = 1/n |
| 3 | 3  | 2.981 | 3.024 | 0.338,0.181,0.093,0.047,0.024,0.011 = 3/n |
| 4 | 6  | 5.698 | 5.906 | → 6/n |
| 5 | 10 | 8.909 | 9.309 | → 10/n |

So `R_r = 1 − r(r−1)/(2n) + O((r²/n)²)`, deficit = the **pair-collision count** `C(r,2)` (each of
the `C(r,2)` index pairs among the `r` summands contributes one `−1/n` connected correction). Two
consequences:

* **`R_r < 1` strictly for every finite n, approaching 1 from below — never crossing.** The
  sub-Wick / `AwaySupBound` inequality holds with a positive, computable margin at ALL tested
  depths and sizes. Both the proven r=2 rung AND the first-open r=3 rung obey it cleanly (no
  crossing at n up to 256) — fresh quantitative evidence the r=3 rung is TRUE.
* **Prize-depth margin (typical):** at `r ≈ ln q ≈ 109`, `n = 2^30`, the expansion parameter
  `r²/n ≈ 1.1e−5 ≪ 1` (perturbative regime valid), giving `R_r ≈ 1 − 5.5e−6 < 1` — comfortable
  sub-Wick margin. This is why the moment method recovers the prize bound for typical primes.

**Honest scope (critical).** This law is measured at ONE (smallest) Burgess prime per n — it is the
**typical/average** behavior. The prize is a **worst-case-over-primes-and-b** statement; specific
"bad" primes with wraparound resonances can spike `R_r` above the smooth law (this is exactly the
Paley/BGK average-vs-worst-case gap, `C∈[1.07,1.49]` worst-case in the dossier). So the pair-collision
law characterizes the typical spectrum precisely and explains why numerics favor the floor being TRUE
— but it does NOT resolve the worst-case, which remains the open core. NOT a prize proof.

## 9. Moment ratio is self-averaging over primes  [sharpens the crux]
`probe_r25_worstcase_primes.py`, 300 Burgess primes per n: `R_2 ∈ [0.9366,0.9369]` (n=16, spread
3e−4), `R_3 ∈ [0.8193,0.8204]`; n=32 similar; **0/600 primes have R_r>1**. The DC-subtracted moment
is strongly self-averaging — it hugs the smooth `1−C(r,2)/n` law independent of prime. So worst-case
bad-prime behaviour does NOT surface in `R_r` (an L^{2r} spectral average); it lives in individual
`|η_b|`, which the moment method smooths over. Upshot: the floor `R_r ≤ 1` holds uniformly over
primes numerically. **The prize is open as a PROOF-uniformity gap at depth `r ≈ ln q` (no technique
bounds the char-p moment there — the Meta-Theorem), not a numerical failure** — the deciding depth
needs `n = 2^30`, brute-unreachable.

## 10. DERIVATION of the pair-collision law — Edgeworth + arcsine kurtosis  [capstone]
The `C(r,2)/n` law is not just a fit; it derives from first principles. Since `−1 ∈ μ_n`, the
imaginary parts cancel and `η_b = Σ_{x∈μ_n} cos(2πbx/p)` is **real** — a sum of `m = n/2` terms
`ξ = 2cos θ` (pairing `x,−x`). For `ξ` with `θ` equidistributed (the pseudorandom model):
`μ₂ = E ξ² = 2`, `μ₄ = E ξ⁴ = 6`, so the 4th cumulant `κ₄ = 6 − 3·2² = −6`, **excess kurtosis
`κ₄/μ₂² = −3/2`** (arcsine law is platykurtic — bounded terms, lighter-than-Gaussian tails).

The Edgeworth correction to the standardized `2r`-th moment of a sum of `m` iid mean-zero terms is
`R_r = 1 + (r(r−1)/6)·(κ₄/μ₂²)/m + O(1/m²)` (one 4-block + (r−2) 2-blocks in the moment–cumulant
partition sum; the block count ratio to `(2r−1)!!` is exactly `r(r−1)/6`). Substituting
`κ₄/μ₂² = −3/2`, `m = n/2`:
`R_r = 1 + (r(r−1)/6)·(−3/2)·(2/n) = 1 − r(r−1)/(2n) = 1 − C(r,2)/n`. ∎ (matches r=2..5 exactly)

**Mechanism, stated plainly:** the subgroup is sub-Wick (`R_r < 1`, floor TRUE) precisely *because*
its spectral terms `2cos θ` are bounded/platykurtic (negative excess kurtosis), so the Gaussian-period
distribution has lighter tails than a true Gaussian and all even moments sit below Wick. This is a
clean structural reason for the floor — new as an explicit statement in this campaign.

**Formalization prospect:** the leading-order statement `E[η_b^{2r}] = (2r−1)!!·σ^{2r}(1 − C(r,2)/n)`
for the equidistributed model is a finite combinatorial identity (moment–cumulant + arcsine moments)
— plausibly Lean-formalizable independent of the prize. The rigorous char-p version needs the
equidistribution/independence of `{2πbx_j/p}` uniformly to depth `r ≈ ln q`, which IS the open
BGK/Paley input — so this derivation cleanly separates the FORMALIZABLE leading term from the OPEN
uniformity, and pinpoints that the entire prize difficulty is the latter.

## 11. FORMALIZED (axiom-clean): the discrete arcsine moment  [landed brick]
`ArkLib/…/Frontier/_R25DiscreteArcsineMoment.lean` — `sum_cos_pow_eq`:
> for `ζ` a primitive `N`-th root of unity in `ℂ` and `N > 2r`,
> `∑_{k<N} (ζ^k + (ζ^k)⁻¹)^{2r} = N · (2r).choose r`.

Axiom-clean (`propext, Classical.choice, Quot.sound`; 0 sorryAx), lands under the real
`autoImplicit=false` build (2959 jobs), lint-clean. Proof: `(ζ^k)⁻¹ = (ζ^{N-1})^k` (nonneg powers)
→ binomial `∑_j C(2r,j)(ζ^{m_j})^k` → `ζ^{m_j}=ζ^j(ζ^{2r-j})⁻¹ = 1 ↔ j=r` (primitive-root
injectivity on exponents `<N`) → geometric sum kills `j≠r`. This is the exact rigorous statement
`E[(2cosθ)^{2r}] = C(2r,r)` over an `N`-grid — the arithmetic core of §10's negative-kurtosis
mechanism, and the FORMALIZABLE leading term isolated from the open uniformity. Mathlib has no such
lemma (upstreamable). This is the honest, provable piece of the moment picture — NOT the prize.

## 12. FORMALIZED sub-Wick suppression + consumer inequality + upstream draft  [steps a/b/c]
Extending §11, the file `_R25DiscreteArcsineMoment.lean` now has FIVE axiom-clean theorems
(real-build 2960 jobs):
* `sum_cos_pow_eq` — the discrete arcsine moment (§11).
* `sum_cos_sq_eq` (=2N), `sum_cos_pow_four_eq` (=6N) — explicit r=1,2.
* `centralBinom_mul_factorial_eq` — **exact sub-Wick suppression:** `C(2r,r)·r! = 2^r·(2r-1)‼`;
  the arcsine moment is exactly `1/r!` of the Gaussian moment of variance 2. Proof via
  `choose_mul_factorial_mul_factorial` + `factorial_eq_mul_doubleFactorial` +
  `doubleFactorial_two_mul`.
* `centralBinom_le_wick` — **consumer inequality** `C(2r,r) ≤ 2^r·(2r-1)‼` (moment-method form:
  arcsine moment ≤ Wick moment; equality only r≤1).
Upstream draft added as **PR-5** in `docs/kb/mathlib-upstream-pr-plan-2026-07-07.md` (Mathlib has
none of these).

**Bridge to the actual `η_b` (step a, honest form).** The in-tree moment identity
`∑_{b} |η_b|^{2r} = p·energyR` (`SubgroupGaussSumMomentLadder.subgroup_gaussSum_moment`) is
unconditional. The formalized arcsine moment gives the EXACT value the per-term `2cosθ` model
predicts, and `centralBinom_le_wick` is the sub-Wick bound a moment-method consumer needs. The one
remaining input — that the actual multiset `{bx mod p : x∈μ_n}` behaves like the equidistributed
grid uniformly to depth `r ≈ ln q` — is precisely the open BGK/Paley uniformity; it is NOT
formalizable as a proved statement (it is the open core), and is correctly left as the named gap.
So steps a/b/c are complete to the honest boundary: everything up to the open uniformity is now
either formalized (b,c) or reduced to the single named open input (a).

## 13. MORE bricks: shifted (autocorrelation) moment + moment→sup engine  [continued build]
Extending the module to **9 theorems** (all axiom-clean, real-build 2960 jobs):
* **`sum_cos_pow_mul_shift_eq`** (NEW): `∑_{k<N}(ζ^k+(ζ^k)⁻¹)^{2r}·(ζ^k)^{2s} = N·C(2r, r−s)` for
  `s ≤ r`, `2r+2s < N`. The `s`-shift Fourier coefficient of the `2r`-th cosine power is the
  off-diagonal central binomial `C(2r, r−s)` — the exact **convolution / autocorrelation** building
  block for the additive-energy structure of `η_b`. Verified numerically (6/6). Recovers
  `sum_cos_pow_eq` at `s=0`.
* **`norm_pow_le_sum_norm_pow`** (NEW): `‖g b₀‖^n ≤ ∑_{b∈s} ‖g b‖^n` — the elementary
  moment→sup reduction that converts any moment bound `∑‖η_b‖^{2r} ≤ B` into the worst-case
  `‖η_b‖ ≤ B^{1/2r}` the prize needs. The engine the whole moment route rests on.

The module `_R25DiscreteArcsineMoment.lean` is now a coherent, self-contained account: exact
discrete-cosine moments (base + shifted) → central binomials; the exact sub-Wick suppression
`C(2r,r)·r! = 2^r·(2r−1)‼` and its inequality; and the moment→sup engine. All prize-independent,
rigorous, upstreamable — the honest formalized skeleton of the moment method, with the single open
input (equidistribution to depth `r≈ln q`) cleanly isolated as the named Paley/BGK core.

## Verdict
All four independent angles land on the same object: the char-p incomplete-Gauss-sum bound at
logarithmic moment depth `r ≈ ln q`, `n = 2^30` — the generalized-Paley eigenvalue / BGK bound,
open in the literature and provably (Meta-Theorem) beyond every elementary door. The fixed-depth
faces are clean; the obstruction is unreachable numerically (needs `n=2^30`) and unresolved
mathematically. **CORE OPEN, ON-BGK. No fabricated closure.** This cycle adds independent
triangulation of the crux, not a breach of it.
