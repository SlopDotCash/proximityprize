# I_∞ campaign — round 4: the multiplier-decay reframing (2026-06-15)

Direct char-0 (`q ≫ n⁴`) computation of the **pure / monomial-direction** incidence
`I(w) = #{ distinct e₁(S) : S ⊆ μ_n, |S| = w, e₂(S) = 0, e₁(S) ≠ 0 }`.
This is the easy (single-direction) sub-object of the prize incidence, but it is exactly
computable and pins the shape of the q-independent count.

## Exact facts established this round

1. **Support law (free-rank / P7 confirmed).** `I(w) > 0` only at `w ≡ 0, 1 (mod 4)`.
   All other bands have no `e₂=0, e₁≠0` w-subset. (Mann/Lam-Leung antipodal parity.)

2. **Closed form on the low-w / capacity plateau — VERIFIED EXACT n=8,16,32,64:**
   ```
   I(w=4) = (n/4 − 1)·n  =  n²/4 − n
   ```
   multiplier `m = I/n = n/4 − 1` for `n = 8,16,32,64 → m = 1,3,7,15`. Quantized to integer
   multiples of n; multiplier set by the core-size spectrum (all `core=2` at w=4).
   **CORRECTED (2026-10-28 audit, T125):** the earlier claim that the multiplier is flat at
   `n/4−1` across the whole low band `w ∈ [4, ρn]` is **false**. Complete exact cyclotomic
   enumeration at `n=16`, `ρ=1/2` (evidence
   `docs/audits/repository-review-2026-10-28/kb42-incidence-plateau-counterexample.json`) gives:

   | w | valid subsets (`e₂=0, e₁≠0`) | distinct `e₁` values `I(w)` | multiplier `I/n` |
   |---|---|---|---|
   | 4 | 48 | 48 | 3 |
   | 5 | 48 | 16 | 1 |
   | 8 | 64 | 48 | 3 |
   | 9 | 80 | 48 | 3 |
   | 12 | 16 | 16 | 1 |
   | 13 | 16 | 16 | 1 |

   So already on the allowed `w ≡ 1 (mod 4)` support band inside `[4, ρn]`, `I(5)=16 ≠ 48`:
   there is no constant plateau 48 at n=16. Subset counts and distinct-image counts also
   differ (w=5: 48 subsets, 16 images), so the two must be reported separately. What survives:
   the w=4 closed form above and the support/parity law in item 1. At n=16 the
   `w ≡ 0 (mod 4)` values `I(4)=I(8)=48` coincide, but no plateau theorem on any band is
   proved; any such statement must name its band and be proved.

3. **⇒ At w=4 the q-independent pure-direction image count is QUADRATIC (`n²/4 − n`), NOT
   `≤ n`** (for n > 8). This refutes the "is the q-independent incidence ≤ n (a
   constant-factor question)" reframing carried from round 3 *for this pure-direction count at
   w=4*. It does not by itself say anything about other w (see the corrected table) or about
   a fixed code's agreement threshold (see the caveat below).

## The corrected, sharpened localization

- Window = `(1−√ρ, 1−ρ−Θ(1/log n))`. The window **edge** is `δ* = 1−ρ−Θ(1/log n)`, i.e.
  *just below capacity* `1−ρ`, so `w* = (1−δ*)n = ρn + Θ(n/log n)` — **just above** the
  capacity-agreement `ρn`.
- Below capacity there is **no** flat plateau: at n=16 the multiplier is 3 at w=4, 1 at w=5,
  3 at w=8 (corrected table above). Only w=4 has a proved closed form (`n/4−1`).
- Past capacity, n=16 shows `w=8,9 → 3n`, then `w=12,13 → n` (multiplier 3→1) over
  `Δw ≈ n/4`; since w=5 already has multiplier 1, the profile is not monotone and "decay"
  here is only a description of these finite rows.
- **Proposed (unproved) reframing as a DECAY-RATE question:** does the multiplier fall to
  `O(1)` (≤ the `q·ε*=n` budget) within the backoff window `w ∈ [ρn, ρn + Θ(n/log n)]`?
  This is a *candidate* reading of the `Θ(1/log n)` in `δ*`, not an equivalence with the
  prize. Caveat: the definition of `I(w)` changes the selected polynomial/constraint family
  with `w` (the subset size enters the constraint), so mapping the profile `w ↦ I(w)` to the
  agreement threshold of **one fixed code/stack** needs a separate bridge that is not proved.
  The characteristic-zero counts also do not automatically give finite-field injectivity or
  worst-direction extremality.

## Honest status vs the 72-sweep verdict

This does **not** escape the open core ([[arklib-407-72-conjecture-sweep]]):
- The above is the **pure monomial direction**. The prize needs the **worst** direction,
  whose plateau count is far larger (72-sweep: 3504 at n=16 on a far band, ≫ the pure 48).
- The **decay rate of the worst-direction multiplier** across the capacity→edge transition
  *is* the Gauss-period / Paley-graph bound in disguise — the same open core, in 6 equivalent
  forms. No new closure.

What survives: (a) the exact closed form `I(4) = n²/4−n` (verified n=8,16,32,64; not a
whole-band plateau — see the corrected table), (b) the `w≡0,1 mod 4` characteristic-zero
support/parity law, (c) a *proposed* decay-rate reframing within the log-backoff window,
which is a heuristic localization only until the fixed-code/threshold bridge is proved.

## Decisive next measurement (not yet run)

Worst-direction multiplier at the window-edge bands `w = ρn + {1,…,n/log n}` for `n = 32, 64`.
Brute force is infeasible (`C(64,32)`); needs the `Z[ζ]` exact + core-stratification method the
orbits-workflow used. Outcome distinguishes: decay-to-O(1) by `w*` ⇒ floor holds (and would be
a real conjecture); multiplier stays super-constant at `w*` ⇒ floor reduces to the open
Gauss-period bound (consistent with the overdetermined 72-sweep conclusion).
