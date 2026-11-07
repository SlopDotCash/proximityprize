# PROVEN norm bound: simultaneous-system bad primes ≤ (2k)^{2k/r} (2026-06-14, wakesync)

> **Guard (2026-10-28 audit, T48; cross T101).** The norm-divisibility argument is valid **for
> dyadic `k`** (`k` a power of two). In that case `r` distinct split conjugate primes give
> `p^r ∣ N(f(ζ))` for the nonzero norm, so `p ≤ (2k)^{2k/r}`. Keep the power-of-two guard, because
> two steps use it. First, `f(ζ^j) = σ_j(f(ζ))` needs every odd `j` to be a unit mod `4k`, i.e. a
> Galois automorphism. Second, `deg f = 2k − 1 < φ(4k) = 2k` needs `φ(4k) = 2k`. Both fail for
> non-dyadic `k`. At `k = 6` (order 24, `φ = 8`) the `±1` polynomial
> `(1+x+x²+x³)(x⁸−x⁴+1)` of degree 11 vanishes at a primitive 24th root of unity in characteristic
> zero (and at `43 ∈ F₉₇`), so the "f ≠ 0 ⟹ f(ζ) ≠ 0" step fails. The `k = 6, 10` scans below are
> therefore outside the proved regime. That example refutes only the single char-0 step at
> non-dyadic order, not the complete simultaneous odd system. As the note itself says, no prize
> closure follows without the missing map from actual window-bad configurations to the complete
> odd system.

## The clean proven mechanism (advances NOVEL-A with a proof, not just empirics)
char-p bad config = sign vector ε∈{±1}^{2k}, f(x)=Σεᵢxⁱ (deg<2k, ±1 coeffs), with f(ζ^{j})≡0 mod p for
the r conditions (ζ a primitive 4k-th root, p≡1 mod 4k; j the odd indices via Newton e_odd=0⟺p_odd=0).
Since f(ζ^j)=σ_j(f(ζ)) are GALOIS CONJUGATES, "f(ζ^j)≡0 mod P for r distinct j" ⟺ r distinct conjugate
primes σ_j^{-1}(P) all divide f(ζ) ⟹ **p^r ∣ N(f(ζ))**. And f≠0, deg f=2k−1<φ(4k)=2k ⟹ f(ζ)≠0 in char 0
⟹ N(f(ζ)) is a nonzero integer with |N| = ∏_{a∈(ℤ/4k)*}|f(ζ^a)| ≤ (2k)^{φ(4k)} = (2k)^{2k}.
⟹ **bad primes satisfy p ≤ (2k)^{2k/r}.**

## The dichotomy, now PROVEN (verified probe_simultaneous_rigidity.py, scans past the bound)
- r=1 (single sum, the additive-coincidence Σ_{s∈S}s≡0): p ≤ (2k)^{2k} — HUGE. FLOPPY. Verified: bad primes
  to 24889 for k=6 (210 of them), to (2k)^{2k} in principle. = NOVEL-C (deployment dirty at scale).
- r=k/2 (full odd system, deg_p H ≤ k/2−1): p ≤ (2k)^4 — poly(k). RIGID. Verified: 0 bad primes past
  (2k)^4 (k=4 to 5000>4096; k=6 to 25000>20736; k=8,10 to thousands).
- General: p ≤ (2k)^{2k/r}, dropping from (2k)^{2k} to (2k)^4 as r grows 1→k/2.

## What this CLOSES (prize scale): the Q1 antipodal-masquerade crux, char-uniformly
For the prize (n=2^30, k=ρn, q≈n·2^128=2^158): (2k)^4 = (2·2^29)^4 = 2^120 (ρ=1/2) **< q = 2^158.** So the
full r=k/2 simultaneous system has NO bad prime ≥ the prize q ⟹ at the prize prime there is NO
antipodal-free config satisfying the full odd system ⟹ the Q1 char-p crux (bad configs forced antipodal)
holds char-uniformly. PROVEN (norm bound), not heuristic. This closes the swarm's "single best forward
bet" (NOVEL-A simultaneous rigidity) — for the antipodal/Q1 face — with a clean proof.

## HONEST: what this does NOT (yet) close — the pivotal unresolved reduction
Whether this pins δ* EXACTLY hinges on ONE unresolved question: **does the δ* window bad config require
the FULL r=k/2 odd system (⟹ rigid ⟹ δ* char-independent ⟹ closure incl. constant), or only the SINGLE
r=1 sum (⟹ floppy ⟹ δ* constant is q-dependent ⟹ BGK/Paley wall on the sharp constant)?**
The swarm's two framings CONFLICT here:
  • Q1 framing: "odd system ⟺ deg H ≤ k/2−1" ⟹ bad config needs r=k/2 ⟹ my bound CLOSES δ* char-uniformly.
  • Grand-unification framing: "δ*-defect = additive-coincidence Σ_{s∈S}s≡0" ⟹ r=1 ⟹ floppy ⟹ wall.
Also: the B-measurement (swarm) shows bad primes fail only the √2 CONSTANT, not the n^{1/2} EXPONENT — so
the δ* FORM 1−ρ−Θ(1/log n) is plausibly char-universal regardless, with only the exact constant (worst
case) at stake. My r=k/2 rigidity would pin the constant too IF the r=k/2 reduction is the right one.
Scale mismatch caution: r=k/2=ρn/2 vs the window agreement-excess ηn~n/log n are different scales; the
exact map from the Q1 2k-subset σ_S to the window agreement set is the missing link.

## Net (honest)
PROVEN the simultaneous-system bad-prime bound p ≤ (2k)^{2k/r}, giving char-uniform rigidity of the full
r=k/2 system at prize scale ((2k)^4 < q) — a clean proof of NOVEL-A's antipodal-rigidity face, replacing
the heuristic. NOT a claimed δ* closure: it pins δ* exactly IFF the δ* window bad config requires the full
r=k/2 odd system (Q1 framing) rather than the single r=1 sum (grand-unification framing). Resolving that
reduction (r=k/2 vs r=1 for the window config) is now THE concrete remaining gap, and it is a definite
finite question, not an analytic wall. probe_simultaneous_rigidity.py.
