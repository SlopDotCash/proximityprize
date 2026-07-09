# A22 — Poisson ceiling census-free pin at n=128 (polynomial threshold, no Thorner–Zaman)

Date: 2026-06-14 · Actionable A22 (`371-T05;371-T06`) · type: lean-brick + probe
Status: **PARTIAL** (real census-free n=128 δ* upper bracket; not the prize window interior).

## What A22 asked

Extend the in-tree `PoissonCeilingFloor` machinery (which dropped the bad-side field-size
threshold from the **exponential** cyclotomic-injectivity bound `(2^μ)^{2^{μ-1}}` to the
**polynomial** bound `p ≥ C(n,d+2)+1`, via `poisson_epsMCA_floor_half`) to instantiate the
census-free bad side at `n = 128`, `d = 2`, and check the "two-octave band admits a certified
Proth prime `h·2^128+1`". Bypass Thorner–Zaman for this instance: first `n = 128` δ* pin at
`ε* = 2^-128`, census-free.

## The math (exact)

For the explicit degree-`≤ d` evaluation code `C = evalCode g n d` (`g` of order `n`) over `F_p`,
the in-tree `poisson_epsMCA_floor_half_int` gives, under

  `p ≥ C(n,d+2)+1`   (polynomial threshold)   and   `(d+2) ≥ (1−δ)·n`   (legal radius gate):

  `ε_mca(C, δ)  ≥  ⌈C(n,d+2)/2⌉ / p`
  ⟹  if `ε* < ⌈C(n,d+2)/2⌉/p` then `δ*(C, ε*) ≤ δ`   (`poisson_mcaDeltaStar_le_floor_half_int`).

### The n=128, d=2 instance (rate ρ = (d+1)/n = 3/128)

- `C(128,4) = 10 668 000`. Polynomial threshold `p ≥ 10 668 001`.
  (Exponential cyclotomic threshold avoided: `128^64 ≈ 7.3·10^{134}`.)
- Legal-radius gate `(d+2) ≥ (1−δ)·n` ⟺ `4 ≥ (1−δ)·128` ⟺ `δ ≥ 1 − 4/128 = 31/32`.
  We pin at `δ = 31/32` (the tightest legal radius `δ = 1 − (d+2)/n`, with equality `4 = (1/32)·128`).
- At `ε* = 2^-128`, the floor `⌈C/2⌉/p` exceeds `ε*` iff `p < ⌈C(128,4)/2⌉·2^128`. Combined with the
  polynomial threshold this is the **prize band** of admissible primes.

### The band is HUGE, not "two octaves"

`scripts/probes/sweep_A22_poisson_pin_n128.py` checks in **exact integer arithmetic**:
band = `[10 668 001, ⌈C(128,4)/2⌉·2^128)` has width `≈ 127` octaves (`log2(upper/lower) ≈ 127.0`).
The actionable's "two-octave" phrasing undersells it — the polynomial threshold is `~2^23` and the
`ε*`-ceiling is `~2^{150}`, so the smooth Proth prime `~2^128` sits comfortably in the middle with
`~18` bits of floor-over-`ε*` slack. (Same `≈127`-octave width for every `(n=2^μ, d)` with `μ ≥ 3`.)

### Certified smooth Proth prime in the band

Want `p = h·2^128+1`: then `2^128 | p−1`, so the order-`128` subgroup `μ_{128} ≤ F_p^×` exists
(the smooth dyadic domain; in fact the full `μ_{2^128}`). Smallest such primes found, each with a
**deterministic Proth certificate** (`a^{(p−1)/2} = −1 mod p`, Proth's theorem, exact integer check):

| h | p = h·2^128+1 | bits | Proth witness a | 128 \| p−1 | in band, pin fires |
|---|---------------|------|------------------|-----------|--------------------|
| 21 | 7145929705339707732730866756067132440577 | 132.39 | 5 | yes | yes |
| 111 | 37771342728224169444434581424926271471617 | 134.79 | 5 | yes | yes |
| 123 | 41854731131275431005995076714107490009089 | 134.94 | 7 | yes | yes |

All band-membership inequalities (`p ≥ C+1`, `2p·ε*_num < C·ε*_den`) and Proth certificates verified
exactly by the probe.

## The Lean brick

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A22_PoissonPinN128.lean`
(namespace `ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22`), built on `PoissonCeilingFloor`:

- `choose_128_4 : Nat.choose 128 4 = 10668000`  (`decide`)
- `radius_gate`  — the legal-radius gate at `δ = 31/32`, `n = 128`, `d = 2` (`4 ≥ (1/32)·128`).
- `poissonPinN128` — for any prime `p` with order-128 `g`, `C(128,4)+1 ≤ p`, and
  `ε* < ⌈C(128,4)/2⌉/p`: `δ*(evalCode g 128 2, ε*) ≤ 31/32`.
- `poissonPinN128_eps128` — the `ε* = 2^-128` specialization.
- `band_ceiling_suffices` — reduces the analytic `ε*`-ceiling to the decidable integer inequality
  `2p ≤ ⌈C(128,4)/2⌉·2^128`.
- `poissonPinN128_band` — fully integer-side: `C(128,4)+1 ≤ p ∧ 2p ≤ ⌈C/2⌉·2^128 ⟹ δ* ≤ 31/32`
  at `ε* = 2^-128`. The Proth prime `21·2^128+1` satisfies both integer side-conditions (probe).

The primality `[Fact p.Prime]` and `orderOf g = 128` stay honest hypotheses: a `decide` primality
proof for a 133-bit modulus is out of kernel reach, but the Proth certificate establishes both
classically — so the instance is real, not vacuous.

**Verification.** `scripts/pg-iterate.sh` ✅ OK (377s); every declaration is axiom-clean
`[propext, Classical.choice, Quot.sound]` with 0 `sorryAx` (file footer `#print axioms`).
`choose_128_4` (`Nat.choose 128 4 = 10668000` by `decide`, `maxRecDepth 4000`) verified axiom-free.

## Honest scope / what's left

- This is a **census-free δ\* UPPER bracket** at `n = 128`, `ε* = 2^-128`, with a **polynomial**
  field-size threshold and an explicitly certified **smooth** Proth prime. Thorner–Zaman is bypassed
  for this instance. That is a real, axiom-clean advance on the bad side at `n = 128`.
- It is **NOT the prize δ\***. The degree-`≤2` code has rate `ρ = 3/128`, and the bracket
  `δ* ≤ 31/32` sits at the **high-`δ` end**, far above the prize window interior
  `(1−√ρ, 1−ρ−Θ(1/log n))` at `ρ ∈ {1/2,…,1/16}`. The Poisson floor is **silent** in that
  interior: there the legal radius forces `d+2 ≈ (1−δ)n` with `δ` near `1−ρ`, so `C(n,d+2)` is a
  middle binomial `≈ 2^{n·H(ρ)}` and `C(n,d+2)/q ≪ ε* = 2^-128` once `q ~ n·2^128` — the floor
  drops below `ε*` and pins nothing. The Poisson lever pins only the **near-degenerate (large-`δ`,
  small-`d`) corner**, exactly the regime where `C(n,d+2)` is polynomially small so the polynomial
  threshold `p ≥ C+1` is achievable below the `ε*` ceiling.
- Take-away: the polynomial-threshold Poisson floor is a clean, Thorner–Zaman-free pin **for the
  small-degree corner**, and it confirms the bad side scales to `n = 128` without analytic NT — but
  it does not reach the rate-`ρ` window interior where the prize δ* lives. The Thorner–Zaman supply
  is needed precisely for the **middle-binomial** rows (`B3` s=128), not for this corner.

## Artifacts

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A22_PoissonPinN128.lean`
- Probe: `scripts/probes/sweep_A22_poisson_pin_n128.py`
- This note.
