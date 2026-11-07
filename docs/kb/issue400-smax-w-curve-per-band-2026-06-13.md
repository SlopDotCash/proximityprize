# Per-band s_max(w) curve: #bad = n·#orbits, q-independent; non-monotonic, peaks s_max=3 near w≈n/2 (2026-06-13)

Building on the signed-single decomposition (`e_1=Σ_singles ±ζ^j`, #bad = #distinct e_1). Computed the
per-band curve `s_max(w)` and `#bad(w)` (= #distinct e_1 over valid `e_2=0` sets of size w). Valid sets
exist only for `w ≡ 0,1 mod 4` (since C(w,2) must be even for the +h-balance). `probe_smax_w_curve.py`.

## n=16 curve
| w | δ=1−w/n | #bad | #orbits=#bad/n | s_max |
|---|---|---|---|---|
| 4 | .75 | 48 | 3 | 2 |
| 5 | .69 | 16 | 1 | 1 |
| 8 | .50 | 48 | 3 | 2 |
| 9 | .44 | 48 | 3 | 3 |
| 12 | .25 | 16 | 1 | 2 |
| 13 | .19 | 16 | 1 | 1 |

## Growth law (across n, fixed small w)
`#orbits(w=4) = n/4 − 1` (=1,3,7,15 for n=8,16,32,64) ⟹ `#bad(w=4) = n(n/4−1) = Θ(n²)`, matching
`s_max=2 → Θ(n²)`. So #bad GROWTH in n is governed by s_max(w): `#bad(w) = Θ(n^{s_max(w)})`.

## Honest complication (why this is NOT yet δ*)
The curve `s_max(w)` is **non-monotonic** in w and `s_max=3` appears only in a NARROW band near `w≈n/2`
(at n=16, only w=9). If the band radius were naively `δ=1−w/n`, the "#bad large" region would be a
middle band (δ≈1/2), not a one-sided threshold — which is NOT how δ* behaves. So:
- The combinatorial `s_max(w)` / `#bad(w)` is a REAL q-independent object (the genuine bad-scalar count
  per band-parameter w), verified.
- But the map `w ↦ actual MCA band δ` is NOT simply `1−w/n`; the calibration (which w, which direction,
  which agreement radius corresponds to the MCA threshold) is the missing piece. Without it, `s_max(w)`
  does not pin δ*.

## Status (honest, no overclaim)
SOLID: signed-single decomposition; `e_2=0 ⟺ P(ζ)²=P(ζ²)` (verified 50626 cases); `#bad=Θ(n^{s_max(w)})`;
the per-band curve + `#orbits(w=4)=n/4−1` law.
*(Scope correction 2026-10-28, audit T48: `#bad = Θ(n^{s_max(w)})` and `#orbits(w=4) = n/4 − 1` are
fits to finite data (four values of `n` for the latter), not proved asymptotics. The counts are
characteristic-zero computations, so "q-independent" needs a characteristic-transfer hypothesis:
the step `e_2 = 0 ⟺ p_1² = p_2` needs `2` invertible, and further Newton steps need their indices
invertible.)* OPEN/UNCLOSED: (i) closed `s_max(w)` formula (non-monotone,
global s_max grows 2,3,4,≥6 — no formula yet); (ii) the band-calibration `w ↦ δ` that would turn the
curve into δ*. RETRACTED earlier: `s_max=μ−1` (false at n=64). No δ* closure; genuine q-independent
structural data committed.
