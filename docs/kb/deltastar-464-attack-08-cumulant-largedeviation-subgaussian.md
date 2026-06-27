# Attack #08 — Cumulant / large-deviation: exploit κ₄<0 sub-Gaussian-leaning period (#464)

**Verdict: REDUCES to the depth-`log m` energy wall (BGK/Paley). No bypass.**
Axiom-clean no-go brick landed: `Frontier/_Attack08_CumulantMGFAllOrders.lean`.

## Target

Bound `M = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`, the nontrivial eigenvalue of
`Cay(F_q, μ_n)`, at the prize point (`n=2^30`, `q≈n·2^128`, depth `r ≈ log m ≈ 89`, `β=4`),
WITHOUT the full energy moment `E_r` at depth `log m`. Discharging this discharges the BGK sup-bound
`WorstCaseIncompleteSumBound`, the necessary analytic input to the two-sided δ* pin in
`_PrizeFloorOfBGK.lean`.

## The angle and the proof attempt

The Gauss period over a smooth subgroup is **sub-Gaussian-LEANING**: the 4th cumulant is negative
(`CumulantDyadicDescent`, `CumulantOrderThreshold`), kurtosis `3 − 3/n < 3`. The Chernoff /
large-deviation programme: treat `Z := ‖η_b‖²` as a random variable over uniform `b ≠ 0` and bound
the tail by exponentiating the MGF,

  `P(Z ≥ s) ≤ exp(−t·s)·E[exp(t·Z)]`,   `E[exp(t·Z)] = Σ_{r≥0} (tʳ/r!)·E_r`,

with `E_r = (1/(q−1))·Σ_{b≠0}‖η_b‖^{2r} = (q·rEnergy − n^{2r})/(q−1)` (DC-subtracted; the in-tree
`cumulant_eq`). A genuine sub-Gaussian envelope `E[exp(tZ)] ≤ exp(t·μ + C·t²σ²)` to the tail level
`s ≈ n·log m` would give exactly `M ≲ √(n log m)` — the prize floor — and would, on its face, only
need `μ = E_1 = n` and `σ² ≈ n²` (the second moment, which IS known: `E_2 = 3n²−3n`), the place where
`κ₄<0` lives. If the negative 4th cumulant compounded multiplicatively (à la independent-sum
sub-Gaussianity), the envelope would hold and the deep moments would never be needed.

## The refutation (why it reduces, exactly)

**Lever (a) — does κ₄<0 compound to a sub-Gaussian tail to depth log m? NO.** The MGF is a power
series whose coefficients are the energy moments at *every* order. The Chernoff saddle for a tail at
level `s` with mean `μ` activates the term of order `r* ≈ s/μ`; for `s ≈ n·log m`, `μ = n`, this is
`r* ≈ log m ≈ 89`. So controlling the tail at the prize level requires controlling the MGF up to
order `r* ≈ log m`, i.e. the energy bound `E_r ≤ Wick·n^r` to depth `log m` — *the open core itself*.
The `κ₄<0` improvement fixes only the `r=2` coefficient; it says nothing about the order-89
coefficient. Formally (`truncMGF_mono`, `truncMGF_le_succ`): the truncated MGF is **monotone in every
energy coefficient** and **monotone increasing in the truncation depth**, so no order can be dropped
and a low-order cumulant fix cannot substitute for control at depth. The deepest moment `E_{log m}`
is still adding strictly positive mass at the saddle (`truncMGF_term_pos`).

**Deep cumulant inflation (the known no-go, re-confirmed).** Even granting one tries to certify the
sub-Gaussian envelope via the cumulants `κ_{2r}` directly (`log E[e^{tZ}] = Σ κ_r t^r/r!`), the deep
connected cumulants are **sign-unstable**: `_DoorIVEighthCumulantSignUnstable` records that the
normalized 8th connected cumulant takes BOTH signs across admissible prize primes (probe
`probe_dooriv_eighth_cumulant_multiprime.py`: `n=32 → +0.257, −0.358, −0.358`; `n=64 → +0.415,
−0.056, +1.540`). No universal fixed-sign certificate (`mixed_sign_forbids_universal_fixed_sign`)
can supply a sub-Gaussian envelope past order 4. The negative κ₄ does NOT propagate to a uniform
`κ_{2r} ≤ 0`; the cumulant generating function is not dominated by its quadratic part at depth.

**Lever (b) — Bernstein/Bennett with the proven poly-slack.** `GaussPeriodMomentBoundSlack`
(`worstCaseIncompleteSumBound_of_energyBound_slack`) proves a polynomial slack `S = n^A` is harmless
(it enters only as `S^{1/2r} = exp(A/(β−1)) = O(1)` at `r ≈ log m`). One hopes a Bernstein bound,
which tolerates a polynomial deviation from the Gaussian envelope, suffices. But Bernstein still
needs the variance proxy `σ²` AND a uniform bound on the higher moments `E_r ≤ r!·M_0·(σ²)^{r-1}`
(the Bernstein moment condition) to depth `r* ≈ log m`. That uniform higher-moment condition is
exactly the depth-`log m` energy bound up to a polynomial slack — i.e. `GaussianEnergyBoundWithSlack`
at `r ≈ log m`, the open named conditional. Bernstein relocates but does not remove the depth-`log m`
energy requirement.

**Lever (c) — exponential-moment / Chernoff from `Σ_b η_b^r = q·N₀ − n^r`.** This identity feeds the
MGF its coefficients exactly, but it is the SAME object: `E_r = N₀(μ_n, 2r)/(q−1)`-scaled additive
relation count. Controlling it to depth `log m` is the additive-relation-count CRUX (BCHKS 1.12 /
distinct subgroup subset-sums), per `CumulantDyadicDescent`'s honest scope note. The dyadic descent
captures only the diagonal `2·N₀(H,r)`; the cross-resonance terms (73–86% of the mass at `r≥2`) are
the wall.

**The proven validity wall (`CumulantOrderThreshold`).** Independently, the moment/cumulant
extraction gives `M_r² ≥ q^{1/r}·n`, so it beats the trivial `M ≤ n` only at order `r > log_n q`,
while its Wick input `CumulantEnergyBound` is provably FALSE past the DC crossover at `r ≈ log_n q`
(Fermat refutation `not_cumulantBound_of_excess`). Useful regime and valid regime are disjoint. The
large-deviation route, being the moment method exponentiated, inherits this wall verbatim.

## The lever that WOULD crack it (and why it is the wall)

The single missing input is: **a uniform sub-Gaussian (or poly-slack-sub-Gaussian) bound on the deep
cumulants `κ_{2r} ≤ 0` (or `|κ_{2r}| ≤ poly·(σ²)^r`) up to `r ≈ log m`.** That is logically
equivalent to `E_r(μ_n) ≤ n^{O(1)}·(2r−1)‼·n^r` at depth `log m` — the DC-subtracted poly-slack
energy bound, the named open core. The κ₄<0 lever is real but *local to r=2*; the sign-instability at
r=8 shows it does not globalize.

## Honest verdict

This is a genuine **no-go for the large-deviation route**, not a closure and not a bypass. The
landed brick (`_Attack08_CumulantMGFAllOrders.lean`, axiom-clean) records the structural reason:
the Chernoff bound is monotone in every energy coefficient and the saddle order for the prize tail is
`r* ≈ log m`, so the route cannot terminate before depth `log m` and reduces to the same BGK/Paley
energy wall. The sub-Gaussian-leaning κ₄<0 is a one-order phenomenon that the sign-unstable deep
cumulants prevent from compounding. Slack + low cumulants do NOT suffice.

**Reduces-to-paley.** Open input: `GaussianEnergyBoundWithSlack μ_n r (n^{O(1)})` at `r ≈ log m`
(equivalently uniform deep-cumulant sub-Gaussianity).
