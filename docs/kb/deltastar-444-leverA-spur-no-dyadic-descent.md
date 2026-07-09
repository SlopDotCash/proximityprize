# #444 Lever-A: the char-p surplus Spur_r does NOT admit a dyadic descent (born-at-top)

Date: 2026-06-17. Honest NO-GO. No bound on `Spur_r` claimed.

## Question (Lever-A)

The char-0 additive energy `E_r^{c0}(mu_n)` is CLOSED via Lam-Leung ±-pairing — a 2-power
identity (vanishing sums of `2^mu`-th roots are ±-paired) — and it TELESCOPES under the dyadic
descent `mu_n -> mu_{n/2}` (squaring; Sweep_A47 `dyadic_telescope`). The open core is the char-p
**surplus**

    Spur_r(mu_n; p) := E_r(mu_n over F_p) - E_r^{c0}(mu_n)  >= 0

= exactly where ±-pairing FAILS mod p. **Does the surplus telescope too?** I.e. is there a
recursion `Spur_r(mu_n) <= f( Spur_*(mu_{n/2}) )` that, with a base case, would bound `Spur_r`?

## Calibration (load-bearing, reproduced before any claim)

Exact BRUTE char-0 baseline (the synthesis formula `(2r-1)!!n^r` is only an UPPER bound; using it
would inflate the baseline and HIDE real surplus). Closed forms found and verified n=4,8,16,32:

    E_1^{c0} = n
    E_2^{c0} = 3 n^2 - 3 n          (NOT 3 n^2; the -3n is the finite ±-pair correction)
    E_3^{c0} = 15 n^3 - 45 n^2 + 40 n

e.g. E_2(mu_8)=168, E_2(mu_16)=720, E_3(mu_16)=50560, E_2(mu_32)=2976 — matches in-tree
`probe_char0_energy_check_407.py`. BabyBear(2^27|p-1)/KoalaBear(2^30|p-1) char-0 proxy:
`Spur_2 = 0` for n=8,16,32 (no short relation vanishes mod a ~10^9 prime). Calibration PASSED.

## Verdict: NO descent. The surplus is BORN AT THE TOP level.

Probe `probe_444_leverA_spur_dyadic_descent.py` computes `Spur_r(mu_n)` and `Spur_*(mu_{n/2})` on
the SAME prime `p == 1 mod n` (so `mu_{n/2}` = squaring image of `mu_n`, both inside `F_p`), at
n=8,16,32, r=1,2,3. Findings:

- **Monotone descent FALSE.** `Spur_r(mu_n) <= Spur_r(mu_{n/2})` fails everywhere; the ratio
  `Spur_r(mu_n)/Spur_r(mu_{n/2})` grows (up to 296× at n=16 p=97 r=3) — the surplus EXPANDS going
  up, it does not contract.

- **DECISIVE — born-at-top (33 witnesses).** `Spur_r(mu_n) > 0` while `Spur_*(mu_{n/2}) = 0` for
  ALL `* <= r`. Cleanest: n=8 p=17 (`mu_4` totally clean, `mu_8` surplus 96/10440); and the whole
  block n=32 p∈{353,449,577,641,673,929,1153} (`mu_16` totally clean, `mu_32` carries Spur_2). So
  the defect appears at full level n with NOTHING downstairs to inherit it from. Any recursion
  `Spur_r(mu_n) <= f(Spur_*(mu_{n/2}))` would force `Spur_r(mu_n)=0` on these — contradiction.
  **No such recursion can exist.**

## The structural reason (why ±-telescoping breaks for the surplus)

Every char-p surplus at depth r is carried by a short (`<= 2r`-term) ±1 relation among the n-th
roots that vanishes mod p but not in `Z[zeta_n]`. The squaring map `mu_n -> mu_{n/2}` only sees
carriers `alpha in Z[zeta_{n/2}]` = the squares (even exponents). Enumerating ALL short ±1
relations that carry the surplus (probe inline check):

- n=8 p=17: **136** carriers, **0** live in `mu_4`, **all 136** need a primitive 8th root (odd
  exponent). Example carrier `alpha = zeta^0 - zeta^1 + zeta^5`.
- n=32 p=353: **896** carriers, **0** in `mu_16`, **all 896** need a primitive 32nd root.
  Example `alpha = zeta^0 - zeta^1 + zeta^{10}`.

So 100% of the surplus carriers use the PRIMITIVE n-th root that the squaring map destroys. The
char-0 side telescopes because ±-pairing is preserved under squaring (the square of a paired
vanishing sum stays a paired vanishing sum). The char-p surplus is precisely the FAILURE of that
identity, and that failure is created by relations through `zeta_n` primitive — invisible after
squaring. **This is the mechanistic explanation of why the wall resists dyadic descent.**

## Consequence

Lever-A (dyadic recursion on the surplus) is a no-go: the surplus does not descend, so a base
case cannot bound it. This is consistent with — and explains — the converged synthesis
(`_DyadicRecursionDstar` REFUTED, `m*` linear not log) and the consolidation verdict
(`deltastar-444-unifyA-supply-eq-demand-consolidation.md`): the wall is one char-p defect object
`{p : p | N(alpha)}` for a short signed `2^mu`-root relation, and that object is generated at the
FULL level, not built up dyadically. No bound on `Spur_r` is claimed; the 25-year thin-subgroup
BGK wall stands.

## Artifacts
- `scripts/probes/probe_444_leverA_spur_dyadic_descent.py` (calibration + descent test + carrier check)
- calibration cross-ref: `scripts/probes/probe_char0_energy_check_407.py`
