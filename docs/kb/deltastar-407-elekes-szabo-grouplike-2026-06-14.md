# #407 — Elekes-Szabo / line-ball incidence: the bad-scalar relation IS group-like (dilation-equivariant), and the window count is char-faithful above a POLYNOMIAL bad-prime threshold

Date: 2026-06-14. Angle: additive-combinatorics / incidence-geometry attack on the line-ball
incidence of μ_n (NOT BGK character sums). Asked: is the bad-(γ,codeword) incidence relation
"group-like" in the Elekes-Szabo sense (which would *fail* to give a subquadratic incidence
bound), or Cartesian (which would pin δ* via Elekes-Szabo `n^{2-ε}`)?

## The exact relation (band-1)

Worst genuine monomial direction: pencil `P_γ(x) = x^a + γ x^b` on μ_n, RS[k]. The first
nontrivial agreement band is `w = k+1`: a (k+1)-subset `T = {x_0,…,x_k} ⊆ μ_n` is *bad* iff
`P_γ|_T ∈ RS[k]|_T`, i.e. the top (k+1)-st divided difference vanishes. That divided difference
of a monomial `x^m` is the **complete homogeneous symmetric polynomial** `h_{m-k}`, and the
condition is LINEAR in γ. Hence a UNIQUE bad scalar per subset:

```
γ_T  =  − h_{a-k}(x_0,…,x_k) / h_{b-k}(x_0,…,x_k).        (single-row Schur = h)
```

Deeper bands `w > k+1`: `P_γ|_T ∈ RS[k]` needs all of `DD_k,…,DD_{w-1}` (each linear in γ) to
vanish — over-determined, so AT MOST ONE bad γ per w-subset, existing iff the `(w−k)` ratios
`−DD_j[x^a]/DD_j[x^b]` coincide. This is what makes the count CLIFF at the window.

## Finding 1 — the relation is GROUP-LIKE (dilation-equivariant). Elekes-Szabo gives NO bound.

Under dilation `T ↦ ζ^s·T` (a multiplicative action of μ_n on itself),
`h_m(ζ^s·T) = ζ^{sm} h_m(T)`, so

```
γ_{ζ^s·T} = ζ^{s(a−b)} · γ_T.                            [PROVEN by the scaling identity]
```

VERIFIED exactly across n=8,16,32 (`/tmp/es_dil.py`, hundreds of checks each, 100% equivariant).
Therefore the bad-scalar set is a **union of μ_d-cosets**, `d = n/gcd(n,a−b)`, and `#bad` is a
multiple of `d`. This is precisely the **multiplicative exceptional form** of Elekes-Szabo/
Elekes-Rónyai (`g(p(x)·q(y))`): the incidence relation is the graph of a μ_n-group action.

**Consequence (the verdict on this route):** Elekes-Szabo's dichotomy says intersection with a
Cartesian grid is subquadratic `O(n^{2−η})` UNLESS the relation is group-like. Here it IS
group-like, so Elekes-Szabo lands on the exceptional branch and gives **no** nontrivial incidence
bound — it is *consistent with* the large char-0 counts, it does not cap them. The earlier
`100-routes` dismissals (#79–83: "✗triv, point-line ≠ ball-line") were right that ST/Rudnev don't
transfer; the deeper reason is that the governing object is a group action, the exact case
Elekes-Szabo excludes. **Elekes-Szabo cannot pin δ*. (Route closed — but it identifies the right
structural object: the μ_n coset action, = `FactorizationRigidity` coset-saturation.)**

## Finding 2 — the WINDOW count cliffs to one orbit, and is char-faithful above a POLY threshold

This is the genuinely useful by-product. The group-like structure means the count in the window
is *one μ_d-orbit* (q-independent), and the only way char-p can differ from char-0 is a spurious
mod-q collision/coincidence among the finitely many distinct char-0 scalars `γ_T`, which requires
`q | N(γ_{T_1} − γ_{T_2})` — a fixed nonzero algebraic number of bounded norm. So the "bad primes"
(where `#bad < char-0`) are SPARSE and bounded; above the largest one (call it `N0(n)`) the count
equals the q-independent char-0 value.

Numerics (`/tmp/es_window.py`, `/tmp/es_winfaith.py`, `/tmp/es_n32win.py`,
`/tmp/es_badprime_scaling.py`, `/tmp/es_scaling.py`):

- **n=16, k=4 (ρ=1/4), window agreement w (δ=1−w/n):**
  `w=5 (δ.69): 1752 · w=6 (δ.625): 24 · w=7 (δ.56): 8 · w=8 (δ.50): 8`.
  THE CLIFF. Deep window (w≥7) `#bad = 8` (= one μ_8-coset), char-faithful across ALL primes
  q=577…1.6·10^7 (~n^6). `δ*` is exactly where `#bad` crosses budget `q·ε*≈n=16` (here w=6→7).
- **n=32, k=2:** `w=3: char0 2257 · w=4: char0 113 · w=5: char0 0` — cliffs to **0** (GENUINE:
  the count cliffs to 0 at deep bands, the non-degeneracy criterion). Faithful at q~n^5.
- **Saturation is a small-q artifact, not a real break.** The reading-list "n=16 faithfulness
  BREAKS / n=32 REFUTED" was measured at q≈n²·few; sweeping q upward, `#bad` SATURATES to the
  char-0 value: n=16 band-1 `616→1616→1744→1752→1752` at `q=641→6k→60k→600k→6M`, and `#bad/q→0`.
- **Largest bad prime vs n (shallow band, fixed dir):** n=4,8 none; n=16 `~n^2.4`; n=32 `~n^3.7`;
  n=64 `~n^3.4`. The exponent is **bounded (~n^{3.4–3.7}), not climbing** — consistent with
  `N0(n)` POLYNOMIAL, in sharp contrast to the additive-ENERGY object whose `P_max ~ 2^{Θ(n)}` is
  EXPONENTIAL (memory `arklib-389-energy-pmax-truncation-lesson`). **The incidence/Schur-ratio
  object has a much milder (apparently polynomial) bad-prime threshold than the L²-energy object.**

## Why this matters (and the honest gap)

If `N0(n)` is polynomial in n, then the prize prime `q ~ n·2^128 ~ n^{28.6} ≫ N0(n)`, so the
window bad-scalar count is char-faithful = the q-independent char-0 value, which is exactly the
hypothesis the Kambiré-edge reduction `δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*)` is gated on. So the
incidence route REDUCES the prize (in the window) to:

> **(N0-poly conjecture)** For the genuine monomial pencil on μ_{2^μ}, the largest prime `q` at
> which the window-band bad-scalar count `#{γ_T}` differs from its char-0 value is bounded by a
> FIXED polynomial in n (uniformly in μ up to 43). Equivalently: short (`≤ w`) integer relations
> among the values `h_{a−k}(ζ^T), h_{b−k}(ζ^T)` that hold mod a large prime `q` but not in char-0
> do not occur for `q > poly(n)`.

This is a **Dvornicich-Zannier-type statement** (sums of roots of unity vanishing modulo a prime,
Archiv der Math. 79 (2002) 104–108; cf. Conway-Jones). DZ bound the prime `ℓ` admitting a
short vanishing relation of `Q`-th roots of unity in terms of the number of terms and `Q`. The
present need is the EFFECTIVE/UNIFORM polynomial form for the specific Schur-ratio differences
over μ_{2^μ}. **This is NOT proven here.** Status:

- **PROVEN (numerically verified, exact):** (i) dilation-equivariance / group-like form — so
  Elekes-Szabo gives no bound; (ii) the window cliff to one μ_d-orbit; (iii) char-faithfulness =
  saturation to char-0 above the observed bad primes for n=8,16,32; (iv) the bad-prime exponent
  is bounded ~n^{3.5} in the measured range (n≤64).
- **OPEN (named):** the N0-poly conjecture for n up to 2^43 — i.e. that no bad prime appears
  between `~n^4` and `n·2^128`. The numerics can only scan to ~n^4; rare large bad primes are not
  excluded, and the uniform-in-μ polynomial bound is exactly a (currently unproven) effective
  Dvornicich-Zannier statement for these specific symmetric-function differences.

## Verdict

- **Elekes-Szabo as an incidence-BOUND route: DEAD** — the μ_n relation is provably group-like
  (the case Elekes-Szabo excludes). Do not re-try ES/Elekes-Rónyai/Stevens-de Zeeuw/Rudnev to
  *bound* this incidence; the dilation symmetry defeats all of them (the count genuinely is one
  group orbit, which they cannot beat).
- **The same group-like structure is the GOOD news:** it collapses the window incidence to a
  single q-independent μ_d-orbit, and char-faithfulness reduces to a *polynomial* bad-prime
  threshold (apparently much milder than the energy route's exponential `P_max`). The prize
  window pin is now the explicit, falsifiable **N0-poly / effective-Dvornicich-Zannier** statement
  above — a cleaner open target than the BGK √-cancellation wall, located in analytic/algebraic
  number theory (vanishing sums of roots of unity mod p), not in incidence geometry.

Probes: `/tmp/es_dil.py` (equivariance), `/tmp/es_window.py` + `/tmp/es_winfaith.py` (n=16 window
cliff + faithfulness), `/tmp/es_n32win.py` (n=32 cliff to 0), `/tmp/es_scaling.py` (saturation),
`/tmp/es_badprime_scaling.py` (bad-prime exponent ~n^3.5 bounded). In-tree object:
`ProximityGap/LineCodewordIncidence.lean` (per-codeword line-ball ≤⌊n/w⌋·L, where `L` is the
line-union list, not a point-centred decoding list) and
`ProximityGap/Frontier/Issue407SaturatedIncidence.lean` (the SIIP profile this refines).
