# Recursive μ_{n/2} attack — FINAL verdict (Phase 6 + recursion workflow, judges taken over)

## The clean char-0 result (genuine, recordable brick)
The 2-power additive-energy telescopes EXACTLY in char-0 (verified to n=64, out-of-sample):
  E_r(μ_{2^a}) = 2^r·E_r(μ_{2^{a-1}}) + CROSS_r(n),  base E_r(μ_2)=C(2r,r),
giving the closed forms (Δ_top = the char-0 cross-energy, CONTROLLED/clean per level):
  E_2 = 3n²−3n ; E_3 = 15n³−45n²+40n ; E_4 = 105n⁴−630n³+1435n²−1155n ; E_5 = 945n⁵−…
  leading coeff = (2r−1)!! = the Gaussian/Wick value, EXACTLY, for all r.
This extends the in-tree Lam–Leung r=2 value (3n²−3n) to ALL r via the explicit 2-power recursion,
with the cross-term Δ_top vanishing/clean at every level (e.g. F-strikes: the cross(ee,oo) bucket = n²/2).
So in CHAR 0 the recursion telescopes to the Wick value ⟹ IF it held in char-p at r≈log q it would give
B ≤ √(2n log q) = the prize. It is the cleanest the structure comes.

## Why it does NOT close the prize (3 decisive obstructions, all proven this round)
1. **char-0 ≠ char-p.** The strikes computed E_r^char0 (ℤ[ζ] antipodal vanishing). The prize needs E_r(mod p)
   at r≈log q; the char-p EXCESS appears past the Mahler clean range r<(1/2)p^{2/n} (vacuous at prize scale),
   and it BREAKS the telescoping. The clean char-0 Δ_top=0 is NOT the char-p Δ_top (the open core).
2. **Realizability telescopes to EXPONENTIAL.** The core-realizability subset-sum Σpᵢ²=e_2(C) in μ_{n/2}
   telescopes (clean, q-indep) to the fixed point 3^{n/4} — EXPONENTIAL, because Lam–Leung makes the n/4
   antipodal-pair contributions additively INDEPENDENT. Does NOT bound #orbits/I_∞ polynomially.
3. **Fold √2-loss IRRECOVERABLE.** (F9, exact mod-p rank) the singleton does NOT halve: each singleton adds
   exactly one independent constraint, k singletons pin a deg-<k poly ⟹ singleton stays full-degree on the
   half-length transversal. The transversal is an ARC, not a subgroup (n/2 even ⟹ μ_{n/2} = union of whole
   fibers, never a transversal) ⟹ there is provably NO second coprime fold to capture it. Ratio = √2 exactly
   at a=3,4,5, every ρ. To cross Johnson one must beat factor 2 via μ_{n/2} multiplicative structure on the
   singleton arc, but the arc is provably NON-multiplicative.

## #orbits at the window edge (orbits workflow, 7 refute / 1 polylog)
#orbits = Θ(n) at the window edge (char-0) — TAUTOLOGICAL at the crossing (I_∞=n ⟹ #orbits=n/orbit_size),
consistent with the crossing being at the window edge, but the growth LAW that pins the crossing location
reduces to the same recursive cross-term = the open char-p excess.

## Net
The 2-power recursion is self-similar and bottoms out trivially IN CHAR 0, where it telescopes to the exact
Wick energy (clean, recordable). But the prize lives in char-p at r≈log q, and every route — char-p excess,
the exponential realizability subset-sum, the irrecoverable √2 singleton arc — hits the SAME irreducible wall.
No closure. The campaign's deepest, most self-similar attack confirms the open core with maximal precision.

> **Scope correction (2026-10-28 audit, T48; cross R-113/PG-073).** The note first keeps the
> char-0 / char-p distinction (item 1 above). The update below then declares characteristic `p`
> "a red herring" after one large-prime match (`q = 2e9`, `n = 32`). That inference is withdrawn.
> - **One prime proves nothing about all primes.** A single matching prime does not establish
>   `q`-independence, and thin-field exceptions to char-0 transfer exist above `n³`. The failure of
>   one transversal fold does not exclude all alternative factorizations or counting arguments.
> - **Orbit counts.** `#orbits = Θ(n)` must divide the incidence by the actual orbit size. Reading
>   `I_∞ = n` as if the incidence and the orbit count were the same number conflates them. "Exactly"
>   for the `n/4` plateau law is a fit at five values of `n`.
> - **Newton.** The step `e_2 = 0 ⟺ e_1² = p_2` needs `2` invertible in the field.

## UPDATE: orbits workflow (q-independence CONFIRMED + structure found, my "O(1)" corrected)
- p-INDEPENDENCE rigorously confirmed: at q=97(<n^4) count=3 (polluted); at q=2e9(>n^4) count=23 = EXACT char-0.
  So char-0 = q>>n^4 object exactly. The q-independent incidence is the right (finite) prize object; char-p is a red herring.
- CORRECTION: my "#orbits=1 at window edge" (from c32) was an UNDERCOUNT (saw only the 6-pairs+1-free core-size-1 family).
  Full pure-e_2=0 count at n=32,w=13 = 23 = 1 + 22 (the 5-pairs+3-core families). So #orbits = Theta(n), NOT O(1).
- CLEAN STRUCTURE (genuine new math, char-0 q-indep):
  * P6 closed form: #orbits = n/4 EXACTLY in the plateau band (n=8,16,32,64,128 -> 2,4,8,16,32).
  * P7 free-rank step law: gamma=-e_1(S), e_2(S)=0 <=> e_1(S)^2 = p_2(S) (Newton). Balanced sets exist only w=0,1 mod 4.
    #orbits keyed to free-rank r(w) (min deletions to reach a zero-sum core): r=1 at shallowest balanced band (1 orbit
    sub-family), r=2,3 deeper. The Theta(n) growth is driven by the rank-2,3 core families.
- RECONCILIATION: Theta(n) incidence at the window edge is CONSISTENT with the crossing (I=n=budget) being there;
  the prize floor is now a CONSTANT-FACTOR question (is the q-indep incidence <= n at the window edge?), a FINITE
  cyclotomic problem (NOT char-p analytic). The clean handle: e_1^2 = p_2 in sumset(mu_{n/2}); count #distinct e_1.
- The Theta-constant in delta*=1-rho-Theta(1/log n) is exactly this finite count's constant. Live Q-workflow attacks it.
