# The Fable FS arc (#466, 2026-07-09): the annihilator ledger — almost-all-primes r=3 Wick rung, sealed to the δ* interface

**TL;DR.** Nine rounds (FS1–FS9), all landed on `fork/main`, seven axiom-clean Lean bricks +
two probe/refutation entries. New method: the **annihilator ledger** — every depth-3
wraparound solution of `μ_n` (2-power `n = 2^{k+1}`) is a nonzero pattern polynomial in
`ℤ[X]` owning a cyclotomic-resultant annihilator `N(g) = Res(x^{2^k}+1, g)` of explicit
dyadic height; a (prime × pattern) double count caps how many primes can carry excess.
Composed with the exact decomposition `addEnergy3 = (15n³−45n²+40n) + wraparoundExcess`
(field-free trivial count = the E3-strata `negSymCount` closed form, via a sign-twisted
bijection), the r53 headroom weld, and the r54 spectral chain, the arc proves, END TO END
with NO named hypotheses:

> For any finite family `P` of primes `≥ 2^s`, at all but
> `≤ n⁶·((k+4)n/s)/(45n²−40n+1) ≈ n⁴(k+4)/(45s)` primes of `P`, in every field of that
> characteristic with a primitive `n`-th root:
> `GaussianEnergyBound (μ_n) 3` (exact Wick), hence `‖η_b‖⁶ ≤ 15qn³` for all `b ≠ 0`,
> hence `WorstCaseIncompleteSumBound ψ μ_n ((15qn³)^{1/3})`.

## Files (all `Frontier/`, axiom set `[propext, Classical.choice, Quot.sound]`)

| brick | file | content |
|---|---|---|
| FS1 | `_FS1Depth3AnnihilatorLedger` | abstract double count + height cap (`t` distinct primes ≥ 2^s dividing `N ≤ 2^L` ⟹ `t ≤ L/s`) + Markov bad-prime cap |
| FS2 | `_FS2PatternAnnihilatorResultant` | `N(g) ≠ 0` (Φ_{2^{k+1}} irreducible /ℚ) and `p ∣ N(g)` at common-root primes — via Mathlib's new resultant API |
| FS3 | `_FS3AnnihilatorHeightBound` | `|N(g)| ≤ (m+d)!·B^{m+d} ≤ 2^{(k+1+b)2^{k+1}}` (Sylvester + `Matrix.det_le`) |
| FS4 | `_FS4Depth3PatternDecomposition` | EXACT `addEnergy3 = trivialCount + wraparoundExcess` (fold monomials; pointwise indicator split) |
| FS5 | `_FS5TrivialCountClosedForm` | `trivialCount = negSymCount G 6` (coeff r of pattern poly = signed multiplicity of ±ζ^r) ⟹ unconditional `Depth3ExcessBounded` |
| FS6 | `_FS6AlmostAllPrimesWickRung` | the composed cap + good-prime Wick weld |
| FS8 | `_FS8PerFrequencyAlmostAllPrimes` | per-frequency `‖η_b‖⁶ ≤ 15qn³` at good primes (r54 chain discharged there) |
| FS9 | `_FS9WorstCaseBoundAlmostAllPrimes` | `WorstCaseIncompleteSumBound` at `M₃ = (15qn³)^{1/3}` at good primes (δ*-interface) |

Refutations: FS7 (Mahler-average height gains only the constant 0.35 — `β ≳ 6` intrinsic);
orbit-shift quotient Markov-neutral (FS6 entry).

## Honest scope

Almost-all-primes, non-vacuous only for prime families at `β ≳ 6`; the prize shape
(`β ≈ 5.3`) is uncapped; the deep-`r` (`r ≈ ln q`) tower — the Paley/BGK wall, the δ* core —
is untouched. Depth-3's sup-norm window (`β < 3`) is disjoint from the cap window (`β ≳ 6`).
This is a structural localization: the r=3 rung's obstruction is now an explicit finite
per-prime pattern count with a proven prime-averaged budget.

## Next named lanes

1. **r=4 mirror**: everything is depth-generic except the char-0 closed form — needs
   `negSymCount G 8` (= `1680h⁴̄ + 5040h³̄ + 2380h²̄ + 70h`, h = n/2; derived, unformalized).
2. **T=1 depth-generic variant**: cap primes with ANY nontrivial vanishing pattern at depth
   r (needs only the char-0 ≤ Wick bound, in-tree via `CharZeroEnergyMultinomial`) — one
   theorem for all fixed r, thresholds `β ≳ 2r+2`.
3. **Which-primes-divide structure**: beating `β ≈ 6` needs control of which window primes
   divide pattern resultants — that is the per-prime uniformity wall itself.

DISPROOF_LOG tags: `466-FS1` … `466-FS9`. Memory: `issue466-fable-fs-arc-almost-all-primes-r3`.
