
> **Scope note (2026-10-28 audit, T48).** The "δ*" values below are binding radii over the swept
> direction family (`j ∈ [k+1, k+5]`). They are not the MCA `δ*`, which needs the maximum over
> all stacks. The char-uniformity is agreement at the tested primes, which is finite evidence and
> not a characteristic-transfer theorem; any transfer claim needs a norm or finite-bad-prime
> exclusion.

## LARGE-N CONFIRMATION (took over stuck workflow agent; efficient barycentric method)
Pushed the binding-radius char-uniformity test to n=20,24 with a UNIFIED apples-to-apples barycentric
method (identical j-range JR=[k+1..k+5] and dedup for char-0 over C and char-p over F_q, q ≫ n³):
- n=16 k=8 (ρ=1/2) sanity: binding a*=11, char-p=char-0=4 (a=11,12), =132 (a=10). UNIFORM. ✓
- n=20 k=5 (ρ=1/4): binding a*=9 (δ*=0.55, in-window), char-0=char-p=0 for primes ≫n³. UNIFORM.
- n=20 k=10 (ρ=1/2): binding a*=13 (δ*=0.350, in-window), char-0=char-p=0. UNIFORM.
- n=24 k=3 (ρ=1/8): binding a*=7 (δ*=0.708, in-window), char-0=char-p=0. UNIFORM.
- **n=24 k=6 (ρ=1/4), NONZERO binding (best test): binding a*=10 (δ*=0.583, in-window),
  char-p = char-0 = 12 at a*=10 for ALL proper primes {13873,13921,14281} ≫ n³=13824;
  =56 at a=9 (δ>δ*), =0 at a=11. FULLY CHAR-UNIFORM around δ*.**

METHODOLOGICAL NOTE (important): a naive run showed char-p=0 vs char-0=12 at n=24 a=10 — this was a
J-RANGE ARTIFACT (the fast pass only swept j≤k+3; the worst direction at a=10 is j=k+4). With matched
j-ranges the discrepancy vanishes (char-p=char-0=12). Any future char-p≠char-0 claim must first rule
out a j-range / dedup mismatch before being read as a refutation.

VERDICT: cliff confinement (binding-radius char-uniformity) HOLDS at every tested (n≤24, ρ∈{1/8,1/4,1/2})
in the prize-faithful regime (proper subgroup, q≫n³). Combined with the swarm's n=32 (ρ∈{1/4,1/8})
this is consistent, multi-method evidence. The only open question remains ASYMPTOTIC: does the
char-faithfulness threshold at δ* stay poly(n³) as n→∞ (n=64 = C(64,9) solves is the compute wall).
