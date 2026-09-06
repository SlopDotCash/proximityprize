# The Paley/BGK Conjecture for thin 2-power subgroups: why it is true, why it is hard, and what could break it

*An essay and ranked attack plan (#444, 2026-06-21). Honesty contract: nothing here proves the
conjecture. The goal is to lay out the problem honestly, propose genuinely-untried machinery, rank
it by feasibility, and then attack each candidate to either refute it or carry it toward a proof.*

---

## 1. The object and the conjecture

Let `p` be a prime, `n = 2^μ | p−1`, and `μ_n ⊂ F_p^×` the group of `2^μ`-th roots of unity (a thin
cyclic subgroup). For `b ∈ F_p` set the **Gauss period**
`η_b = Σ_{x∈μ_n} e_p(b x)`, `e_p(t)=e^{2πi t/p}`, and the **sup-norm / Paley-graph eigenvalue**
`M(μ_n) = max_{b≠0} |η_b|`. The thin regime is `β := log_n p = 4` (`n ≈ p^{1/4}`), the regime the
Reed–Solomon proximity prize lives in.

> **Paley/BGK conjecture.** `M(μ_n) ≤ C·√(n·log p)` with `C` an absolute constant, **uniform in `p`**.

Equivalently (Liu–Zhou): `Cay(F_p, μ_n)` is **near-Ramanujan**. Equivalently (moment form): the
DC-subtracted energy `tilde-E_r = p^{-1}Σ_{b≠0}|η_b|^{2r} ≤ K^r·(2r−1)‼·n^r` uniformly to depth
`r ≈ ln p`. These three faces are identical; I will move between them freely.

The trivial bounds bracket it: `√n ≤ M ≤ n` (lower by Parseval/Alon–Boppana, upper by the triangle
inequality). The conjecture asks for the lower end, `√n` up to `√(log p)`. The best **proven** bound
is Bourgain–Glibichuk–Konyagin (2006): `M ≤ n^{1−δ}` for an *ineffective* `δ>0` (`n^{1−o(1)}`). The
gap from `n^{1−o(1)}` to `n^{1/2+o(1)}` is a **full half-power** and has been open ~20 years.

## 2. Why I believe it is true

The campaign accumulated strong, exact, non-circumstantial evidence:

1. **The char-0 shadow is provably Gaussian.** `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r` for *all* `r`
   (proven, axiom-clean, via Lam–Leung 2-power antipodal balance + `I₀(2x) ⪯ e^{x²}`). So the
   "free" version of the bound holds exactly; only the char-`p` wraparound `W_r = E_r^{F_p}−E_r^{char0}`
   is in question.
2. **The spectral distribution is `n`-universal and sub-Gaussian.** Exact computation (n=32,64,128):
   `|η_b|/√n` has an `n`-independent distribution (mean 0.80, std 0.60) with tail
   `−ln P(>t) ≈ c·t²`, `c≈0.6`, ruling out exponential tails. The max over `~p` samples then sits at
   `√(ln p / c)`, and indeed `M/√(n log p) ∈ {1.18, 1.49, 1.10}` for n=32/64/128 — a **bounded band**
   over a 4× range of `n`.
3. **The wraparound is sparse and structured.** `W_r = 0` at all but a density-`d(n)` set of "bad
   primes", and `W_r = Σ_{D∈R_r(n)} mult(D)·[D(g)≡0 (mod p)]` — a finite sum of `p`-independent
   weights gated by local divisibility (exact, 100% of primes tested). It is not a wild object.

The honest counterweight: the moment ratio `K_max(n) = (E_r^{F_p}/Wick)^{1/r}` at the saddle **grows**
(`~n^{0.77}`), so the *energy* is genuinely super-Wick even though the *max* stays bounded. The bound
is true about the **max**; it is false about the **bulk energy**. That tension is the whole problem.

## 3. Why it is hard — three barriers, each proven in-tree

1. **The √-cancellation barrier.** Every route ultimately needs `√q`-cancellation in a sum of `n`
   structured unit vectors with no main term — `|Σ_{x∈μ_n} e_p(bx)| ≤ √n·polylog`. There is no
   curvature (`μ_n` is 0-dimensional, flat) and no main term to extract; the cancellation must come
   from arithmetic alone.
2. **The K-moment / for-all-`q` barrier (proven).** Any *finite* moment method gives exponent
   `½ + β/(2K) > ½`; reaching `½` needs *all* moments to depth `r≈ln p` controlled *uniformly*, and
   the energy ratio diverges (`K_max~n^{0.77}`). The moment/energy face is *necessity-only*
   (`moment_ladder_exceeds_prize`) — it reformulates the wall, it cannot bypass it. The max-vs-bulk
   gap means any method that "sees the bulk" (energy, L², triangle-over-twists) overshoots.
3. **The thinness barrier (sum-product out of regime, proven).** Sum-product / Bourgain–Garaev
   self-improvement needs `|G| > p^δ`; the prize is `β=4`, i.e. `|G| = p^{1/4}` — *at* the Burgess
   edge, where the multiplicative-energy excess that sum-product converts into a saving is **zero**
   (`E_2(μ_n) = Θ(n²)`, Sidon). The bootstrap *anti-contracts* in thinness (ceiling exponent
   `(β+2)/4`, proven `_AvW14`).

## 4. Why every current machinery falls down — the precise mechanism

| Machinery | Falls down because |
|---|---|
| Weil/Deligne (single fiber) | `μ_n` 0-dim ⟹ main term IS the count; no `√p` saving |
| Deligne over the config variety | per-slice Betti `n`-independent, but triangle over `m^{2r}` twists overshoots Wick by `2^{40000+}` — needs `√`-cancellation **across** coherent twists, which (`_AvW15` analysis) is the wall at doubled depth |
| Moment / energy ladder | super-Wick at saddle (`K_max~n^{0.77}`); sees bulk, not max |
| Sum-product / Bourgain–Garaev | out of regime at `β=4`; no energy excess to convert |
| Decoupling / restriction / VMVT | need curvature; `μ_n` flat, `Σ\|η_b\|²=pn` trivial Plancherel |
| Soft analytic pivot (Dirichlet) | closes the **ceiling** (needs only prime *existence*); the floor/wall need a *cancellation* no existence argument supplies; super-thin makes the bound **vacuous** (`_AvW13`) |
| Delsarte LP / association scheme | degree-1-blind; LP optimum `= p−n` ⟹ vacuous `M ≤ √(p−n)` |

The unifying diagnosis: **the bound is about the maximum of a flat, thin, arithmetic spectrum, and
every available tool either needs geometry the spectrum lacks (curvature, dimension), or reads the
bulk instead of the max, or needs the subgroup to be thicker than `β=4` allows.**

## 5. Candidate NEW machinery — genuinely untried in this campaign

These are *not* in the 25-direction map; each is proposed with its hope and its likely failure mode.

**T1. Higher-order Fourier analysis / Gowers `U^k` inverse theorem.** The additive energy is the
`U²` norm; deeper moments are `U^k`. The inverse theorem (Green–Tao–Ziegler) says a large `U^k` norm
forces correlation with a degree-`(k−1)` nilsequence. *Hope:* `μ_n` (a multiplicative subgroup)
should NOT correlate with polynomial-phase/nilsequence structure, forcing small Gowers norms ⟹ the
energy bound. *Risk:* the inverse theorem is qualitative; making it quantitative-uniform in `p` at
the saddle depth is itself a hard open problem, and the nilsequence obstruction for multiplicative
subgroups may be exactly the cyclotomic structure that creates the wraparound.

**T2. Polynomial method / slice rank / Croot–Lev–Pach.** The bad configurations are the zero set of
the vanishing-sum system `Σ x_i = Σ y_i` over `μ_n^{2r}`. *Hope:* a slice-rank / partition-rank
upper bound on the solution set, exploiting that `μ_n` are roots of `X^n−1` (a sparse polynomial),
gives a count strictly below the trivial — the CLP method famously beats "obvious" counts for
sparse algebraic sets. *Risk:* slice rank bounds *sizes* of progression-free sets, not *energies*;
the vanishing-sum variety is high-dimensional and CLP may give nothing past `r=2`.

**T3. Fouvry–Kowalski–Michel trace-function amplification.** `η_b` is (nearly) a trace function of
bounded conductor; FKM provides `√q`-cancellation for sums of trace functions AND an amplification
method to average over a family beating Weil. *Hope:* amplify over the family `{b}` to extract a
sub-Weil saving. *Risk:* the conductor of the relevant sheaf grows with `n` (the `m^{2r}` twists),
so the amplification gain is eaten by the conductor — likely the same wall.

**T4. Transference / dense model (Green–Tao–Ziegler).** Transfer the bound from a dense model where
BGK is easy. *Hope:* if `μ_n` satisfies a Hardy–Littlewood majorant / linear-forms pseudorandomness
condition, the sparse bound follows from the dense one. *Risk:* `μ_n` is multiplicatively (not
additively) structured and almost certainly fails the additive pseudorandomness the transference
needs — likely refuted fast.

**T5. Sum-of-squares / Positivstellensatz with a uniform-in-`r` certificate.** Seek a degree-`d` SOS
certificate of `Wick_r − tilde-E_r ≥ 0` whose *structure* is uniform in `r` (a single "template"
certificate that instantiates at every depth). *Hope:* the antipodal/2-power symmetry gives a
low-degree SOS template; machine-find it at small `r`, prove it extends. *Risk:* SOS degree for the
energy inequality grows with `r`; the uniform template is exactly the uniformity that is the wall —
but it is *computable*, so it can be tested decisively.

**T6. Bourgain–Gamburd spectral gap on the 2-adic tower.** Use the tower `μ_2⊂⋯⊂μ_n` and a
spectral-gap/expander-mixing argument rather than the (refuted) naive recursion. *Hope:* a
super-approximation / spectral-gap statement for the tower of Cayley graphs. *Risk:* the naive tower
recursion `M(2n)²≤2M(n)²` is numerically false (ratios →3.86); the spectral-gap framing likely
inherits the same obstruction.

## 6. Ranking by feasibility × likelihood

Feasibility = can we make concrete, decisive progress (compute / derive / refute) in-session.
Likelihood = chance the tool, if it worked, actually yields the `√q`-cancellation.

| Rank | Tool | Feasibility | Likelihood | Net | Why ranked here |
|---|---|---|---|---|---|
| 1 | **T2 polynomial method / slice rank** | HIGH | LOW–MED | **best first** | concrete, computable, genuinely untried, sparse-polynomial structure is exactly CLP's wheelhouse; decisive either way |
| 2 | **T1 Gowers `U^k` inverse** | MED | MED | **most promising if it works** | the "right" framework for energy; the one tool whose natural output IS a max/structure dichotomy, not a bulk bound |
| 3 | **T5 SOS uniform template** | HIGH | LOW | computable refutation | testable decisively at small `r`; if a uniform template exists it is the prize |
| 4 | **T3 FKM amplification** | MED | LOW | likely conductor-wall | worth a precise conductor computation to confirm/deny |
| 5 | **T6 spectral-gap tower** | LOW | LOW | likely reduces | naive version already no-go |
| 6 | **T4 transference** | MED | VLOW | likely fast refute | μ_n almost surely fails additive pseudorandomness |

## 7. The attack plan

Attack in rank order, each to a *decisive* verdict (refute, reduce-to-wall, or genuine-advance →
adversarial re-verification). Priorities: **T2 and T1 first** (the genuinely-untried, highest-net),
then **T5** (computable refutation), then confirm **T3/T4/T6** reduce. An "advance" is only accepted
after a harsh independent re-derivation rules out circularity / finite-size illusion / hidden
reduction — the standard for a 20-year-open problem.

*This essay claims no proof. It is the honest map of the terrain and the ranked plan; the attacks
follow.*
