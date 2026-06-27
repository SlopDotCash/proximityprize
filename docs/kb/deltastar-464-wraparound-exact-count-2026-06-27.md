# The wraparound exact count `W_r` — per-configuration inclusion–exclusion (#464, 2026-06-27)

**Target:** `brick-wraparound-exact-count`. Get an EXACT/sharp inclusion–exclusion for the char-`p`
wraparound surplus `W_r = p(E_r − V_{2r})`, connect the land-exhaust finite-bad-prime (resultant)
enumeration to `W_r`, and decide whether `W_r ≤ p(Wick − V_{2r}) + n^{2r}` is provable for GOOD
primes by a clean argument leaving only "prize prime is good".

**Lean brick:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WraparoundExactCount.lean`
(axiom-clean: `propext, Classical.choice, Quot.sound`; real `lake build`, 3297 jobs, passes
`autoImplicit=false`).

## The exact identity (NEW, probe-verified 100% on `n=4,8`, `r=2,3`)

For `p ≡ 1 (mod n)`, write each ordered pair `(A,B)` of size-`r` multisets of `ℤ/n` as a
**configuration** `c` (exponent-difference vector), with multiplicity `N(c)`, char-0 value
`poly_c(ζ) = Σ c_k ζ^k`, and mod-`p` value `poly_c(w)` (`w` = chosen primitive `n`-th root in `F_p`).

```
   Σ_c N(c)                      = n^{2r}                          (every ordered config)
   Σ_{c : poly_c(ζ)=0} N(c)      = V_{2r}                          (char-0 energy, ≤ Wick)
   E_r^{F_p}  =  V_{2r}  +  Σ_{c : poly_c(ζ)≠0} N(c)·[poly_c(w)≡0]  (mod-p energy = char-0 + wrap)
```

Hence the **exact inclusion–exclusion** (the asked "(configs) × (p | resultant)" shape):

```
   W_r / p  =  Σ_{c : poly_c(ζ)≠0}  N(c) · [poly_c(w) ≡ 0 mod p]   (EXACT — verified n=4,8 r=2,3)
```

`[poly_c(w)≡0] = 1 ⟹ p | Res(Φ_n, poly_c)`, so each active config is a prime factor of a
configuration resultant — the **direct generalization of the land-exhaust width-four
(`r=2`) `canonicalRatioBadPrimes` to arbitrary depth `r`.**

### Exact bad-prime characterization (probe, 100% match)

`W_r(p) > 0 ⟺ p ∈ (⋃_{c : poly_c(ζ)≠0} primeFactors(Res(Φ_n, poly_c))) ∩ {p ≡ 1 mod n}.`

| `n` | `r` | empirical `W_r>0` primes | resultant-set `∩ (p≡1 mod n)` |
|----|----|----|----|
| 8 | 2 | `{17, 41}` | `{17, 41}` |
| 8 | 3 | `{17,41,73,89,97,137,313}` | `{17,41,73,89,97,137,313}` |
| 4 | 3 | `{5, 13}` | `{5, 13}` |

## The bounds (all proven in the brick)

* **`wrap_le_nonzero_total`** (unconditional, cleanest): `W_r/p ≤ n^{2r} − V_{2r}`. Numerically
  `W_r ≤ p(n^{2r} − V_{2r})`, verified for all tested primes.
* **`wrap_le_asked_budget`** (the asked target): `W_r/p ≤ (Wick − V_{2r}) + n^{2r}`. The `+n^{2r}`
  is **load-bearing**: the sharper `W_r ≤ p(Wick − V_{2r})` is FALSE at bad primes (e.g. `n=8 r=3
  p=17`: `W_r/p = 10440 > Wick − V = 2560`).
* **`goodPrime_wrap_eq_zero`** (the clean argument): if every char-0-nonzero config has
  `poly_c(w) ≢ 0` (i.e. `p` avoids ALL config resultants), then `W_r = 0`, so `E_r^{F_p} = V_{2r}`
  exactly, and `E_r^{F_p} ≤ Wick` follows from the proven char-0 bound — the **entire prize-floor
  energy bound, conditional only on "prize prime is good".**

## Does this bypass the Paley wall? NO — but it localises it sharply.

The per-config resultant has the elementary envelope `|Res(Φ_n, poly_c)| ≤ (2r)^{n/2}` (each
`|poly_c(root)| ≤ Σ|c_k| ≤ 2r`, over `deg Φ_n = n/2` roots). The dichotomy:

* **Fixed `r`** (char-0 closed-form regime `r ≤ 9`; width-four `r = 2`): bad-prime union is
  **finite**, ceiling `(2r)^{n/2}` — the land-exhaust regime, dischargeable by Thorner–Zaman /
  Linnik prime-avoidance. **Genuinely Paley-independent.** (`resultantHeightEnvelope_widthFour`
  records `4^{n/2} = 2^n`, matching `canonicalRatioPolySharpBound`.)
* **Prize depth `r ≈ ln q`**: the same envelope is `(2r)^{n/2} = 2^{Θ(n)}`, the `2^{Θ(n)}` height
  the campaign has confirmed ≥60× as the wall. "Prize prime is good" at depth `ln q` **reduces to
  Paley.** (`resultantHeightEnvelope_mono`: deeper ⟹ larger bad-prime ceiling.)

So the brick is an **exact structural reduction** of `W_r` to configuration resultants (and a real
Paley-independent discharge at *fixed* depth), but the prize-depth `goodPrime` hypothesis is itself
the Paley/BGK obligation. **NOT prize closure.**

## Exact missing piece (clean Prop)

```
GoodPrimeAtPrizeDepth :=
  ∀ c, poly_c(ζ_{2^30}) ≠ 0 → poly_c(w) ≢ 0 (mod p*)   for all configs c of depth r ≈ ln q,
  i.e.  p* ∉ ⋃_{r ≤ ln q} ⋃_{c} primeFactors(Res(Φ_{2^30}, poly_c)).
```

This is the Paley wall: the union has prime ceiling `2^{Θ(n)}`, so it is NOT obviously avoidable by
a polynomial-window prime. At fixed `r` it IS avoidable (the win). The genuinely Paley-independent
content delivered: the EXACT identity, the unconditional budget, and the fixed-depth finite-bad-set
discharge.
