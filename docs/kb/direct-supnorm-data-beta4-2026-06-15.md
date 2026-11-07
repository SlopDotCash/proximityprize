# Direct sup-norm data at prize thinness β=4 (supports "all primes at β≥4")

> **Correction (2026-10-28 audit, T48).**
> - **No "all primes" claim follows.** The table is a finite measurement (`n ≤ 32`, sampled primes).
>   "Holds for EVERY prime at β=4", "the conjecture is TRUE at the prize thinness" and "ALL primes at
>   β≥4" are not established. Recorded thin exceptions exist: at `n = 64`, `p = 17318209`
>   (`p > n⁴`), the additive energy is `E_2 = 13632`, above both the char-0 value `12096` and the
>   Wick value `12288` (T91 / G173; the same cell is recorded as a transfer-false norm-divisor
>   witness in `Research/ProximityPrize/Frontier/_wfS7_galois_spread.lean`). The measurements stay
>   as history.
> - **The norm paragraph overreaches.** The minimum nonzero norm of a short non-antipodal sum is `2`
>   (for example `N(1 − ζ) = 2`), but a minimum controls neither the maximum nor a typical value. It
>   does not show that actual short norms are uniformly small. Nor does it make every norm
>   upper-bound route impossible: a valid nonzero norm upper bound **below** `p` would still rule out
>   `p`-divisibility for the sums it covers. Whether such a bound is usable is a question of actual
>   parameters and heights, not something this probe settles.

Probe (prize-faithful: proper μ_n, p≡1 mod n, p≈n^4 so β=4, multi-prime, never n=q-1; /tmp/prize-research/
almostall*.py). Computed M(n)=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| / √(2n log m), m=(p-1)/n:

| n  | #primes | median | max  | std   | frac M>√(2n log m) |
|----|---------|--------|------|-------|--------------------|
| 16 | 60      | 0.821  | 0.856| 0.014 | 0                  |
| 24 | 40      | 0.942  | 0.971| 0.012 | 0                  |
| 32 | 30      | 0.880  | 0.929| 0.028 | 0                  |

FINDINGS:
- The TARGET bound M ≤ √(2n log m) (constant C=√2) holds for EVERY prime at β=4 in the computable range,
  TIGHTLY concentrated (std ~0.01-0.03), no violations. ⟹ the conjecture is TRUE at the prize thinness with
  the conjectured constant; the open problem is purely the PROOF (deep-moment char-p transfer), not the truth.
- Supports the "almost-all-primes" angle STRENGTHENING to "ALL primes at β≥4" (no bad primes at β=4 here);
  consistent with in-tree thinness-essential (violations only at intermediate-thick β≈2.3-3.2 structured primes,
  OUTSIDE the prize). The tight concentration ⟹ periods behave robustly sub-Gaussian at β=4.
- Caveat: n≤32 is the safe/small computable range; the constant creeps (0.82→0.97→0.93) non-monotonically but
  stays <1. A proof must be thinness-essential (use β≥4; a thickness-monotone method wrongly covers β<4 where
  the bound is FALSE). Does NOT prove the prize (needs the analytic deep-moment bound), but pins the target as
  true + the constant as ~√2 + the bad set as empty at β=4 (computable range).

## Norm-bound route addresses the WRONG quantity (size vs p-divisibility) — probe finding
True min nonzero |N(S)| of a short non-antipodal sum in Z[ζ_{2^μ}] is CONSTANT = 2 (not t^{n/4}):
  weight-2 non-antipodal diff = ζ^a(1−ζ^{odd}), N(1−ζ_{2^μ})=Φ_{2^μ}(1)=2. (Verified n=8,16,32.)
⟹ The cyclotomic-norm UPPER bound (crude t^{n/2}, refined t^{n/4}) is WILDLY loose — actual norms of short
sums are tiny (≈2–poly), far below the ceiling. The spurious-collision obstruction is NOT norm SIZE but
p-DIVISIBILITY: a short S contributes a char-p-extra collision iff p | N(S), and N(S)=2 (weight 2) is never
divisible by the odd prize prime. So improving the norm ceiling (n/2→n/4→…) CANNOT close the prize — it bounds
the wrong object. The real quantity is #{short S : p | N(S)} = the additive-energy excess = BCHKS 1.12.
Heuristic: typical N(S)≈t^{n/4} (random-walk conjugates), p|N(S) w.p. ~1/p, #(weight≤2r S)≈(2n)^{2r} ⟹
spurious start at 2r≈4 log n/log(2n)≈4 (r≈2-3), matching proven char-p=char-0 only for r≤2(3). The conjecture
is that beyond there the p-divisible count stays ≤ Wick (random-like) — the open BCHKS-1.12 core, an arithmetic
(divisibility) not metric (size) statement. CONSEQUENCE for the assault: norm/height-bound angles are
fundamentally size-instruments and cannot reach the divisibility count; the live target is the direct
deep-moment / p-divisible-collision count at r≈log m.
