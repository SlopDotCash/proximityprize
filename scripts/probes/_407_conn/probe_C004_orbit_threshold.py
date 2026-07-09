"""
Probe for connection C004 (rank 4): "δ* count = n·K: the budget q·ε*≈n is exactly ONE μ_n-orbit".

Two distinct claims are tested, in the PRIZE REGIME (dyadic μ_n a PROPER subgroup, large prime q).

CLAIM A (identity / collapse, asserted PROVEN in-tree):
   #bad = n·K + ε,  ε = [0 in badSet],  with quantization in units of n.
   In-tree lemmas (adjacent_card_eq_n_mul_add_zero / n_dvd_card_badScalars_adjacent) prove this
   only for the ADJACENT pair (b = a+1, multiplier g, order n). For a general monomial pair (a,b)
   the multiplier is c = g^(b-a), of order ord(c) = n/gcd(t,n), t=|a-b|. So the quantum is
   n/gcd(t,n), which is < n whenever gcd(t,n) > 1. For DYADIC μ_n (n=2^μ) and EVEN t this is a
   PROPER divisor: the "exactly ONE μ_n-orbit = n" reading then FAILS (the orbit has size < n).

   We verify the EXACT multiplicative-orbit structure of the bad-scalar set directly from the
   far-line / Vieta description:
       lacBad(μ_n,a,t) = { e_t(S) : S ⊆ μ_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 },  t=a-b.
   The orbit-closure law e_t(g·S)=g^t e_t(S) makes this a union of ⟨g^t⟩-cosets; ord(g^t)=n/gcd(t,n).

CLAIM B (threshold, the NOVEL content): "δ* is EXACTLY the radius where K crosses from O(1) to ≥2",
   and the budget I(δ)≤n reads K(δ)≤1+o(1). We tabulate the far-line incidence I(δ) (= #bad for the
   worst monomial direction) versus δ for proper-subgroup primes and locate the K:1->2 crossing,
   comparing to the proven ladder/Johnson reach.

Exact integer arithmetic over μ_n ⊂ F_q*. Small n=8,16; multiple proper-subgroup primes.
"""

import itertools
from math import gcd

# ---------- finite field μ_n machinery (exact) ----------

def find_subgroup_primes(n, beta_lo, beta_hi, want=3):
    """primes q ≡ 1 mod n with q ≈ n^β, β in [beta_lo,beta_hi]; μ_n a PROPER subgroup (n<q-1)."""
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    out = []
    q = lo - (lo % n) + 1
    if q < lo: q += n
    while q <= hi and len(out) < want:
        if q > n+1 and is_prime(q):
            out.append(q)
        q += n
    return out

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d = m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def subgroup_mu_n(q, n):
    """return generator g of μ_n and the list of its elements [g^0..g^{n-1}]."""
    assert (q-1) % n == 0
    # find a generator of F_q* then raise to (q-1)/n
    cof = (q-1)//n
    for h in range(2, q):
        g = pow(h, cof, q)
        if orderOf(g, q) == n:
            elems = [pow(g, i, q) for i in range(n)]
            assert len(set(elems)) == n
            return g, elems
    raise RuntimeError("no generator")

def orderOf(g, q):
    if g == 0: return 0
    x = g % q; o = 1
    while x != 1:
        x = x*g % q; o += 1
        if o > q: return -1
    return o

def esymm(subset, t, q):
    """elementary symmetric polynomial e_t of a list of field elements, mod q."""
    # dp
    e = [0]*(t+1); e[0] = 1
    for x in subset:
        for j in range(min(t, len(e)-1), 0, -1):
            e[j] = (e[j] + e[j-1]*x) % q
    return e[t] if t < len(e) else 0

# ---------- lacBad value set (the bad-scalar set for monomial direction (a,b), t=a-b) ----------

def lacBad(elems, a, t, q):
    """{ e_t(S) : S⊆μ_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 } : the bad-scalar set at radius δ=1-a/n."""
    n = len(elems)
    vals = set()
    for S in itertools.combinations(elems, a):
        ok = True
        for j in range(1, t):
            if esymm(S, j, q) != 0:
                ok = False; break
        if ok:
            vals.add(esymm(S, t, q) % q)
    return vals

def orbit_decompose(vals, g, t, n, q):
    """decompose the value set into ⟨g^t⟩-cosets; report quantum ord(g^t)=n/gcd(t,n) and #orbits."""
    c = pow(g, t, q)             # multiplier
    oc = orderOf(c, q)           # = n/gcd(t,n)
    nonzero = sorted(v for v in vals if v != 0)
    has_zero = (0 in vals)
    remaining = set(nonzero); orbits = []
    while remaining:
        x = next(iter(remaining))
        orb = set()
        y = x
        for _ in range(oc):
            orb.add(y); y = y*c % q
        assert orb <= remaining, (x, orb, remaining)
        orbits.append(orb); remaining -= orb
    return dict(quantum=oc, n_over_gcd=n//gcd(t, n), num_orbits=len(orbits),
                nonzero_count=len(nonzero), has_zero=has_zero, total=len(vals),
                orbit_sizes=sorted(len(o) for o in orbits))

# ---------- run ----------

print("="*78)
print("PRIZE REGIME: dyadic μ_n PROPER subgroup, q≈n^β (β≈4-5), q≡1 mod n, n≪√q")
print("="*78)

for n in (8, 16):
    primes = find_subgroup_primes(n, 4.0, 5.2, want=2)
    print(f"\n##### n = {n} (=2^{n.bit_length()-1}), proper-subgroup primes q = {primes} "
          f"(β≈{[round(__import__('math').log(p,n),2) for p in primes]})")
    for q in primes:
        g, elems = subgroup_mu_n(q, n)
        print(f"\n  q={q}  g={g}  μ_n={sorted(elems)[:6]}... (|μ_n|={n}, q-1={q-1}, "
              f"cofactor={(q-1)//n})")
        # sweep code rate k; direction (a,b)=(k+t,k); radius δ=1-a/n; valid window k<=b<a, a<=n
        for k in (n//4, n//2):    # rate ρ = k/n in {1/4, 1/2}
            print(f"    rate ρ=k/n={k}/{n}={k/n}:  "
                  f"[t | a=k+t | δ=1-a/n | #bad | quantum ord(g^t)=n/gcd(t,n) | "
                  f"#orbits K | sizes]")
            for t in range(1, n-k+1):
                a = k + t
                if a > n: break
                vals = lacBad(elems, a, t, q)
                info = orbit_decompose(vals, g, t, n, q)
                delta = 1 - a/n
                Kdesc = info['num_orbits']
                print(f"      t={t} a={a} δ={delta:.3f} "
                      f"#bad={info['total']:<4d} quantum={info['quantum']:<3d}"
                      f"(n/gcd={info['n_over_gcd']}) K={Kdesc} sizes={info['orbit_sizes']}")
