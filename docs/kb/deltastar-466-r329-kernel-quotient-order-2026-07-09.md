# #466 R329 (Fable): kernel/lattice quotient order = |Res|/p — saturation becomes integer arithmetic

Date: 2026-07-09 · Lane file: `Frontier/_R329KernelQuotientOrder.lean`
(depends on r323; validated after the r323 olean lands)

## Statement chain

For a nonzero relation `d` realized at prime `p` (i.e. `evalVec g d = 0` over `ZMod p`,
`g^{2^k} = -1`):

1. `nat_card_quot_ker_evalHom` — the evaluation kernel `K_p ⊂ ℤ[x]/(x^{2^k}+1)` has index
   exactly `p` (first isomorphism theorem; every ring hom onto `ZMod p` is surjective).
2. `span_relationPoly_le_ker` — the recurrence lattice `L_{P_d}` sits inside `K_p`.
3. `relindex_mul_p_eq_patternResultant` — the index tower gives, exactly,
   `[K_p : L_{P_d}] · p = |Res(x^{2^k}+1, P_d)|.natAbs`.
4. `card_quotient_dvd_of_patternResultant_dvd` — hence R321's saturation hypothesis
   `[K_p : L_{P_d}] ∣ 2^u` is EQUIVALENT to the integer divisibility
   `|Res|.natAbs ∣ 2^u·p`.

## Why this matters

Together with r323 (index = |Res|), r325–r328 (return bound → collision-mass cap), the
saturation route now has a fully machine-checked skeleton whose ONLY analytic input is:

> **(BinomialBadPrimeLaw)** every in-window K-bad prime `p` admits a realized *binomial*
> relation `a + b·x^s` (`|b| < |a|`) with `|Res(x^{2^k}+1, a+b·x^s)| ∣ 8p`.

This is a statement about primes dividing `a^m ± b^m` (the binomial resultant closed
form), verified by the R321/R322 census for all 92 in-window `n=32` cells (cofactor
∈ {2,4,8}, zero odd cofactors). No lattice theory, Fourier duality, or Paley spectrum
remains in the reduction — refute or prove BinomialBadPrimeLaw and the r-fold collision
side of the saturation route closes.

## Honest scope

- The cap is on the *count/mass of short relations* at the fixed prime; converting the
  collision-mass cap into the final DC-subtracted moment inequality still passes through
  the R310/R240 sockets (mass-weight bookkeeping, per-relation mass bound `M`).
- BinomialBadPrimeLaw may be FALSE at larger `n` — it is exactly the right next
  refutation target (census at `n=64` / `m=32`).
