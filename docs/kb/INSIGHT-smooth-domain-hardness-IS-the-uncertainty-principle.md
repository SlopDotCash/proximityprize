# HEURISTIC: smooth-domain hardness in sparse-word experiments tracks the weak DFT uncertainty principle on Z_{2^μ} (#407)

A *heuristic* explanation, supported by finite experiments, for why the smooth domain μ_n (n=2^μ) looks like
the hard case — and a classical frame for an open quantitative question. **Scope correction (2026-10-28 audit,
T123/T110):** the complex prime-order uncertainty theorem quoted below does **not** transfer unguarded to
finite fields (explicit counterexample in the section "Coefficient field matters"), the table's `s*=k+2` and the
displayed derivation `s ≤ k+1` are reconciled below, and the sparse-word maximum `s*` studied here is **not**
the MCA/covering/bad-scalar threshold of the code (a separate worst-word/line bridge is missing).

## The setup (uncertainty-principle reformulation)

The far-line agreement of `x^a+γx^b` with a deg-<k codeword on `S ⊆ μ_n` means the function `P|_{μ_n}` (where
`P = x^a+γx^b−c(x)`) vanishes on `S`. As a function on `μ_n ≅ Z_n`, `P` has **DFT support `{0..k−1, a, b}`**
(size ≤ k+2). It vanishes on `|S|=s` points, so `|supp(P)| = n − s`. The DFT **uncertainty principle** on `Z_n`
relates `|supp(P)|` and `|supp(P̂)| ≤ k+2`. Here `s*` denotes the **sparse-word maximum** = max zeros of such a
`P` over the special two-monomial words `x^a+γx^b` = `n − min|supp|`. It is a maximum over a special word
family, not the worst-received-word list radius, the covering radius (which is `n−k` for any RS code, T110), or
the MCA bad-scalar threshold; relating it to any of those needs a worst-word/line bridge that is not proved here.

## The DICHOTOMY (finite experiments, engine — not a theorem)

| n type | s* (sparse-word max) | 1−s*/n | uncertainty (heuristic) |
|---|---|---|---|
| **PRIME** (17,19,23,29,31) | **k+2 (CONSTANT, observed)** | 1−(k+2)/n | complex prime-order UP is strong; finite-field analogue needs extra hypotheses |
| **SMOOTH 2^μ** (16,32,…) | **grows with n (observed)** | below 1−(k+2)/n | WEAK (maximally composite) |

Observed in the engine's finite-field runs: prime n gives `s*−k = 2` constant across k=3,4,5 and n=17..31;
smooth n=2^μ gives `s*−k` growing (n=16,k=4: 3; larger n: more). These are finite sparse-word experiments.
They do not show that any code is "at capacity" or "only Johnson": that would require the universal
worst-word/line threshold of the code, which this sparse-word maximum does not determine.

## Why this is the mechanism

**Tao's uncertainty principle** (2005, "An uncertainty principle for cyclic groups of prime order",
arXiv:math/0308286) is a theorem about **complex-valued** functions: for n PRIME, a nonzero `f : Z_n → ℂ` has
`|supp f| + |supp f̂| ≥ n+1`. Its proof uses Chebotarev's theorem that every square minor of the complex
prime-order DFT matrix is nonzero. *If* that bound applied, then with `|supp f̂| ≤ k+2` we would get
`n−s+k+2 ≥ n+1 ⟹ s ≤ k+1`, i.e. `s* ≤ k+1`.

### Coefficient field matters (the transfer is guarded)

The prize lives over a finite field `F_p` with `μ_n ⊆ F_p^×`, and there the complex theorem does **not** transfer
unguarded. Counterexample (exact integer arithmetic; evidence
`docs/audits/repository-review-2026-10-28/kb41-finite-field-prime-order-uncertainty-counterexample.json`):
in `F_23` take the prime-order subgroup `μ_11 = ⟨4⟩`. The nonzero three-term polynomial `X + 12X^3 − 13` vanishes at
`1, 4, 18 ∈ μ_11`. As a function on `μ_11` it has support `8` and finite-field Fourier support `3` (exponents
`{0,1,3}`), total `11 < 12 = n+1`. Here `k=1`, Fourier support `k+2`, and `s = 3 = k+2 > k+1`.

So the engine's own observation `s* = k+2` for prime n (table above) is **inconsistent with** the complex bound
`s* ≤ k+1`: the observed finite-field value exceeds what the transferred theorem would allow. That off-by-one is not
a typo to be smoothed over — it shows the complex theorem is not what governs these finite-field runs. A correct
finite-field transfer needs an explicit **nonvanishing-minor hypothesis**: every relevant square minor of the
`F_p`-Fourier (Vandermonde-in-`μ_n`) matrix must be nonzero in `F_p`. Since the complex minors are nonzero
elements of `ℤ[ζ_n]`, this hypothesis holds for all but finitely many primes `p ≡ 1 (mod n)` (those not dividing
the norms of the minors), but it fails at some fields such as `p = 23, n = 11`; it must be checked or assumed, not
inherited from the complex statement.

For **n = 2^μ (the prize)**, n is maximally composite, so even the complex uncertainty principle is **weak**
(subgroup-supported functions vanish on large structured sets) — a (k+2)-Fourier-sparse function can vanish on many
more points. This is a plausible *heuristic* for why the smooth domain behaves worse in the sparse-word
experiments. It is not a proof that prime-order subgroups give capacity or that the 2-power domain sits in a
"Johnson-to-floor" regime for the code's actual MCA threshold: both statements would need (i) the guarded
finite-field uncertainty bound above and (ii) the missing worst-word/line bridge from the sparse-word maximum to the
code threshold (T110).

## The open question, now classically stated

A sparse-word sub-question for n=2^μ is **a quantitative uncertainty principle on μ_{2^μ} ⊆ F_p^×**: what is the
minimum support of a function on `μ_{2^μ}` with Fourier support `{0..k−1,a,b}` (equivalently its max zeros `s*`)?
Is it of order `√(kn)` or `k + Θ(n/log n)`? Answering it would settle only this special-word extremum; it would
bear on the Johnson-vs-floor MCA question only after a worst-word/line bridge is proved. Related literature (note
that most of it is stated over `ℂ`, and the coefficient-field guard above applies to every transfer):
- **Tao (2005)** — complex prime-order case (strong over `ℂ`; finite-field transfer needs nonvanishing minors).
- **Donoho–Stark (1989)** — `|supp f|·|supp f̂| ≥ n` (general; weak, gives the n/(k+2) bound).
- **Meshulam**, "An uncertainty inequality for finite abelian groups" — composite/general groups.
- **Borwein–Erdélyi / Konyagin** — sparse polynomials and roots of unity.
- The uncertainty principle for `Z_{p^k}` / `Z_{2^μ}` specifically is the precise object (divisor-structure dependent).

## Why this matters (the conceptual advance)

This offers a heuristic for the campaign's observation that the 2-power domain behaves worse than prime-order
domains in sparse-word experiments: composite cyclic groups have weaker uncertainty principles. It connects the
sparse-word sub-question to a well-studied area (cyclic-group uncertainty principles). It does **not** explain or
settle the prize threshold: the coefficient-field guard and the sparse-word-to-code-threshold bridge both remain.

## Status

A heuristic frame (smooth-domain weakness ↔ weak uncertainty), supported by finite sparse-word experiments, plus a
sparse-word sub-question stated as a quantitative uncertainty problem on `μ_{2^μ} ⊆ F_p^×`. NOT a closure and not a
theorem about the code's MCA/covering threshold. Corrections: the complex Tao bound is not a finite-field zero bound
without the nonvanishing-minor hypothesis (`F_23`, `μ_11` counterexample above); the observed prime-n value `s*=k+2`
exceeds the would-be transferred bound `k+1`; the sparse-word maximum is not the covering radius or MCA threshold
(T110). Observed (finite runs, not proved): `pg <prime> k` → s*=k+2; `pg <2^mu> k` → s* grows. See also the
adversarial audit in `docs/research/proximity-gap/DISPROOF_LOG.md` ("DFT-uncertainty quantitative core", 2026-06-15),
which finds the smooth-n growth witnesses to be subgroup-supported artifacts and the classical bounds vacuous for
separating Johnson from the floor.
