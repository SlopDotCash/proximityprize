# #444 floor-side [LP-delsarte-on-list]: the μ_n COSET-SCHEME LP is degree-1-blind (B1, WALL)

**Date:** 2026-06-17 · Issue #444 · companion ABF26 (eprint 2026/680).
**Verdict:** **reduces-to-wall (B1).** The sharper *association-scheme* LP — the μ_n coset
(cyclotomic) scheme on the evaluation domain, not the trivial mass-only scheme — gives the **same
Parseval ceiling** as the trivial LP. It is degree-1 / 2nd-moment blind. A genuine sub-result is
proven (the no-go is now stated for the full commutative-scheme constraint class, not just the
mass functional), but **no floor closure**. CORE `M(μ_n) ≤ C√(n log m)` UNCHANGED/OPEN.

## The angle (as assigned)

> FLOOR-SIDE: Linear-programming / Delsarte bound on the worst-case list specialized to RS-on-μ_n
> with the dyadic structure. The list is a code-distance/packing question; an LP dual certificate
> (Delsarte, with the **dyadic association scheme of μ_n**) might bound it. Prior: LP/Delsarte is
> degree-1-blind / phase-blind (`parseval_lp_extremal`, B1). But the **ASSOCIATION-SCHEME LP using
> the μ_n coset scheme** (not the trivial one) is a sharper object. Does the coset-scheme LP give a
> list bound, or is it B1 (2nd-moment blind, caps at Parseval)?

This sharpens dir. 5 of the 25×25 map (`DelsarteLPNoGo.parseval_lp_extremal`), which only killed
the trivial mass-only LP. The open question was whether the **richer coset scheme** breaks Parseval.

## What the probes found (`_probe_444_coset_scheme_lp.py`, `_probe_444_coset_lp_vs_e2.py`, `_probe_444_list_anticode_lp.py`)

1. **The μ_n coordinate coset scheme IS the cyclic scheme C_n — not a richer object.** The
   dilation group μ_n acts on the n coordinates (indexed by μ_n); orbits of ordered pairs `(x,y)`,
   `x≠y`, are indexed by the **ratio** `y/x ∈ μ_n∖{1}`, giving exactly `n−1` nontrivial relation
   classes (verified `7,7,15,15` at `n=8,8,16,16` over `p=17,41,97,193`). This is the
   **commutative** translation scheme of the cyclic group `ℤ/n`; eigenspaces = DFT characters,
   `P`-matrix = DFT. The "dyadic structure" gives the `2^μ` cyclic scheme, still commutative.

2. **A commutative-scheme Delsarte LP is LINEAR in the spectral measure.** Objective `max_J τ_J`
   and all scheme constraints (`τ ≥ 0`, `Q`-positivity `(Pτ)_t ≥ 0`, mass `Σ τ = p−n`) are linear
   in `τ`. The LP value is governed by linear functionals; the only degree-1 datum the scheme
   pins is the total mass `Σ τ = p − n`. So `max_J τ_J ≤ p − n` (`house ≤ √(p−n) ≈ √(nm)`), the
   `√m`-loss Parseval ceiling — a factor `√(m/2log m) ≈ 2^63` (prize `m≈2^128`) above the truth.

3. **E_2 is a 4-point correlation, structurally invisible to a 2-point (pair) scheme LP.** The
   first functional that beats Parseval is `E_2 = Σ_J τ_J² = #{a+b=c+d : a,b,c,d ∈ μ_n}`, a
   **4-point** additive correlation (verified exact `E_2=1104` at `n=16,p=97`; `784` at `p=193`;
   char-0 baseline `3n²−3n=720`). A pair-scheme LP variable encodes only **2-point** ratio-class
   data; `Σ τ²` is a **quadratic** form in `τ`, not a linear functional of the 2-point
   distribution. Making `E_2` linear needs the 4-point (exponential-size, non-commutative) scheme,
   whose "LP" is the full SDP / Lasserre hierarchy — no longer a Delsarte LP.

4. **The classical Hamming-scheme list-anticode LP is vacuously loose at prize rates.** Brute
   check: at `δ ≈` Johnson the list-difference anticode has diameter `2δn = n` (full), so the LP
   bound is the trivial volume `~q^{...}` (`6.98e9` vs true list `1`). The anticode constraint is
   empty at these radii — the Hamming scheme is the wrong scheme, and the right (coset) scheme is
   degree-1 blind by (1)–(3).

## What is formalized (axiom-clean, the genuine sub-result)

`Frontier/CosetSchemeLPNoGo.lean` (`⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`):

- `lp_value_eq_mass_of_linear_certs` — **any** Delsarte/LP value for `max_J τ_J` certified only by
  linear functionals pinning the total mass `Σ τ = S` equals `S` (Parseval). Generalizes the
  mass-only `parseval_lp_extremal` to the whole commutative-scheme constraint class: the
  all-mass-on-one-coset vertex is feasible for every linear-mass-only constraint set, so the LP
  cannot drop below `S`.
- `e2_invisible_to_linear` — **the decisive degree-1-blindness separation.** Two nonnegative
  spectral vectors `τ_A` (all mass on one coset, `max=S`, `E_2=S²`) and `τ_B` (flat, `max=S/m`,
  `E_2=S²/m`) with **identical** mass `S` but **different** house and **different** `E_2`. Any
  linear certificate depending only on the mass takes the same value on both ⟹ cannot separate
  their houses ⟹ `E_2` is invisible to it. This is the formal kernel of "the coset-scheme LP is
  degree-1-blind."
- `energy_is_quadratic_not_linear` — `E_2` fails additivity (`E_2(2τ)=4E_2(τ)≠2E_2(τ)`), so it is
  not a linear functional any LP dual can certify.
- `concentrated_maximizes_both` — house and `E_2` are co-maximized by concentration, yet the mass
  (all the LP sees) is constant across the slice — why pinning the house genuinely requires `E_2`.

## Bucket and bottom line

- **E1 (output the SUP not L2)?** NO — the LP optimum is the Parseval (L2) scale `√(p−n)`, the sup
  improvement `√log` is exactly the gap it cannot see.
- **E2 (genuinely new object)?** NO — the coset scheme is the cyclic scheme C_n, the object IS the
  η_b/Gauss-period spectrum (B2-flavored) and the LP linearizes to the mass moment (B1).
- **E3 (hypothesis holds on flat 0-dim Sidon μ_n)?** N/A — the LP is feasible but vacuous; no
  structural hypothesis is even needed because the bound it yields is already trivial.

**Bucket: B1 (2nd-moment / degree-1 blind), reduces-to-wall.** The sharper coset-scheme LP does
**not** escape; it caps at the same Parseval ceiling because the scheme is commutative (linear)
and `E_2` (the first Parseval-beating functional) is a 4-point object outside any 2-point Delsarte
LP. The floor-side LP/Delsarte angle is a method-class no-go, a companion to `DelsarteLPNoGo`,
`BlockSumNormNoGo`, and the disc(Ψ) no-go. **δ\* OPEN; the live handle remains the nonlinear
`E_r`/BGK wall.** Honesty contract holds — no fabricated closure.
