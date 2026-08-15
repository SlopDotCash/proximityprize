# Issue #466/#505 G124: the moment LP — linear descent constraints on the depth fibers

Date: 2026-07-10

G123's ladder identities are exact but not linear in the depth fibers. G124 extracts the
linear content, making the depth census the feasible set of an explicit LP.

## Results (`Frontier/_G124MomentLPDepthConstraints.lean`, 3 declarations, axiom-clean, 0 sorryAx)

- `descFactorial_le_matchCountM` (**visibility floor**): every pair at cancellation depth `s`
  admits at least `(r−s)_m` ordered m-matchings. Constructed from the landed G87
  maximal-cancellation representation: the two padding complements carry the common part with
  its explicit relative permutation σ, and composing the complement embeddings with every
  `g : Fin m ↪ Fin (r−s)` gives `(r−s)_m` distinct matchings (injectivity via `padSlots`).
- `moment_LP_row` (**the LP**): for every `m ≤ r`,
  `Σ_{s=0}^{r} (r−s)_m · depthFiber A r s ≤ (r)_m² · #A^m · E_{r−m}(A)` —
  a triangular system of LINEAR upper bounds on the depth fibers whose data are the
  lower-rung energies. Deep rows vanish automatically (`(r−s)_m = 0` for `s > r−m`).
- `moment_LP_top_row`: row `m = r` recovers the exact permutation envelope
  `r!·fiber₀ ≤ (r!)²·#A^r`.

## Why this matters

This is the first LINEAR constraint system on the depth census: previous results controlled
fibers one at a time (G97 envelopes) or through non-linear identities (G123). The LP rows are
simultaneous and triangular — row m constrains the depths `0..r−m` with explicit
descFactorial weights, driven by `E_{r−m}`. Combined with the G96/G101 signed objects, any
numerical or theoretical bound on lower-rung energies now propagates to a POLYTOPE constraint
on the whole census at rung r. The fully-disjoint sector has weight 0 in every row `m ≥ 1` —
the LP formalizes precisely that it is the only unconstrained direction (the wall).

## Honest scope

Constraints only; nothing here bounds the fully-disjoint sector. CORE remains OPEN.
