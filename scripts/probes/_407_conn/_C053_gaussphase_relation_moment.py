"""
C053 probe: Gauss-sum DFT identity makes N0 a moment of UNIT phases u_chi (phase-only).

Claim (C053):
  eta_b = (1/m) sum_{chi in mu_n^perp} chibar(b) tau(chi),  |tau(chi)|=sqrt(q)   ... (i)
  sum_b eta_b^r = q * N0(G,r)                                                       ... (ii) (F16)
  => q*N0(G,r) = q*(sqrt(q)/m)^r * sum_{chi_1...chi_r=1} u_{chi_1}...u_{chi_r}      (substitution)
     with u_chi := tau(chi)/sqrt(q) on the unit circle.
  "The amplitude sqrt(q) drops out entirely; N0 is a pure moment of unit phases."

We test, with EXACT setup at proper-subgroup primes (prize regime n=2^mu << sqrt(q)):
  (A) The Gauss-DFT identity (i): eta_b = (1/m) sum_chi chibar(b) tau(chi). [exact, well known]
  (B) The substituted identity: does
        m^r * N0(G,r) / q^{r/2}   ==   M_r := sum_{chi_1...chi_r=1, chi_i in mu_n^perp} u_{chi_1}...u_{chi_r}  ?
      i.e. is N0 literally this phase moment up to the prefactor (sqrt(q)/m)^r * q? We check the
      EXACT rational/complex equality.
  (C) The crux: "amplitude inert / drops out". We test whether M_r tracks N0 with the AMPLITUDE
      genuinely removed -- i.e. whether the magnitude of the house (the actual prize object
      B = max_b |eta_b|) can be read off from a phase-only quantity, OR whether the amplitude
      sqrt(q) re-enters when you pass from the relation-restricted moment to B.

We use F_q with q prime, q = 1 mod n, n = 2^mu a PROPER subgroup, n << sqrt(q).
"""

import cmath, math
from itertools import product

def primitive_root(q):
    # smallest primitive root mod prime q
    phi = q - 1
    fac = set()
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.add(m)
    for g in range(2, q):
        if all(pow(g, phi//f, q) != 1 for f in fac):
            return g
    raise RuntimeError("no primitive root")

def setup(q, n):
    """Return (g, subgroup G = mu_n as list of F_q elements, log table)."""
    assert (q-1) % n == 0
    g = primitive_root(q)
    # mu_n = n-th roots of unity = { g^{(q-1)/n * k} } for k in 0..n-1
    step = (q-1)//n
    G = [pow(g, step*k, q) for k in range(n)]
    # discrete log table base g
    dlog = {}
    cur = 1
    for e in range(q-1):
        dlog[cur] = e
        cur = (cur*g) % q
    return g, G, dlog

def additive_char(q):
    # psi(x) = exp(2pi i x / q)
    return lambda x: cmath.exp(2j*math.pi*(x % q)/q)

def eta(b, G, psi, q):
    return sum(psi((b*y) % q) for y in G)

def N0(G, r, q):
    """N0(G,r) = #{ (y_1,...,y_r) in G^r : sum y_i = 0 in F_q }  (additive r-fold reps of 0)."""
    cnt = 0
    for tup in product(G, repeat=r):
        if sum(tup) % q == 0:
            cnt += 1
    return cnt

def mult_chars_on_subgroup_dual(q, n, g, dlog):
    """
    mu_n^perp = characters chi trivial on... NO. In the Gauss-period picture:
    The relevant characters are the n characters of F_q^* whose ORDER divides...
    Actually for eta_b = sum_{y in mu_n} psi(by), the Gauss-DFT identity uses the m = (q-1)/n
    characters that are TRIVIAL on mu_n, i.e. chi(mu_n)=1, the 'annihilator' mu_n^perp.
    These are chi_t : x -> exp(2pi i * t * dlog(x) / (q-1)) with t a multiple of n...
    let's get it precise below in the identity check.
    """
    pass

def gauss_sum(chi_t, q, g, dlog, psi):
    """tau(chi) = sum_{x != 0} chi(x) psi(x), chi = chi_t : x -> w^{t*dlog(x)}, w=exp(2pi i/(q-1))."""
    w = 2j*math.pi/(q-1)
    s = 0+0j
    for x in range(1, q):
        s += cmath.exp(w*chi_t*dlog[x]) * psi(x)
    return s

def run(q, n, rmax=4):
    g, G, dlog = setup(q, n)
    psi = additive_char(q)
    m = (q-1)//n
    print(f"\n=== q={q}, n={n}, m=(q-1)/n={m}, sqrt(q)={math.sqrt(q):.3f}, n/sqrt(q)={n/math.sqrt(q):.4f} ===")

    # --- (A) Gauss-DFT identity check ---
    # mu_n^perp = { chi : chi(mu_n)=1 }. chi_t(x)=w^{t dlog x}; chi_t trivial on mu_n iff
    # t * dlog(y) = 0 mod (q-1) for all y in mu_n. dlog(y) ranges over multiples of m=(q-1)/n.
    # So need t*m = 0 mod (q-1)  =>  t = 0 mod n. So mu_n^perp = { chi_{n*s} : s=0..m-1 }.
    perp_t = [n*s for s in range(m)]
    taus = {t: gauss_sum(t, q, g, dlog, psi) for t in perp_t}
    # check |tau|=sqrt(q) for nontrivial chi (t!=0); tau(trivial)=-1
    maxnormerr = 0.0
    for t in perp_t:
        if t == 0: continue
        maxnormerr = max(maxnormerr, abs(abs(taus[t]) - math.sqrt(q)))
    print(f"(A) max ||tau(chi)| - sqrt(q)| over nontrivial chi in mu_n^perp: {maxnormerr:.2e}")

    # eta_b vs (1/m) sum_{t in perp} chibar_t(b) tau(chi_t):
    w = 2j*math.pi/(q-1)
    def chibar(t, b):
        return cmath.exp(-w*t*dlog[b])
    iderr = 0.0
    for b in range(1, q):
        lhs = eta(b, G, psi, q)
        rhs = (1/m)*sum(chibar(t, b)*taus[t] for t in perp_t)
        iderr = max(iderr, abs(lhs-rhs))
    print(f"(A) max |eta_b - (1/m) sum chibar(b) tau(chi)| over b!=0: {iderr:.2e}  (Gauss-DFT identity)")

    # --- (B) substituted moment identity ---
    # Claim: q*N0(G,r) = q*(sqrt(q)/m)^r * M_r,  M_r = sum_{t1+...+tr = 0 mod (q-1), ti in perp} prod u_{ti}
    #   where u_t = tau(chi_t)/sqrt(q).  Equivalently  m^r * N0 / q^{r/2} == M_r.
    # NOTE: the additive-relation set {chi_1...chi_r=1} for chi_ti means t1+...+tr = 0 mod (q-1).
    u = {t: taus[t]/math.sqrt(q) for t in perp_t}
    for r in range(2, rmax+1):
        n0 = N0(G, r, q)
        # M_r over r-tuples of perp characters whose product is trivial: sum t_i = 0 mod (q-1)
        Mr = 0+0j
        for tup in product(perp_t, repeat=r):
            if sum(tup) % (q-1) == 0:
                pr = 1+0j
                for t in tup:
                    pr *= u[t]
                Mr += pr
        lhs = (m**r) * n0 / (q**(r/2))   # = m^r N0 / q^{r/2}
        err = abs(lhs - Mr)
        print(f"(B) r={r}: N0={n0:6d}  m^r N0/q^(r/2)={lhs.real:12.4f}  M_r={Mr.real:12.4f} (im {Mr.imag:+.2e})  |diff|={err:.2e}")

    # --- (C) amplitude-inert test ---
    # The PRIZE object is B = max_{b!=0} |eta_b|.  Is it readable from a phase-only quantity?
    # eta_b = (sqrt(q)/m) * sum_t u_t chibar_t(b).  So B = (sqrt(q)/m) * max_b |sum_t u_t chibar_t(b)|.
    # Let P := max_b |sum_t u_t chibar_t(b)|  (the PHASE-ONLY exponential sum, amplitudes all 1).
    # Then B = (sqrt(q)/m) * P EXACTLY. So 'amplitude inert' means: B's size is governed by P,
    # but the conversion factor sqrt(q)/m carries q. The question: does P (phase-only) decouple
    # from q, i.e. is P ~ O(m) (=> B~sqrt(q)) trivial completion, or P ~ sqrt(n*m) (=> B~sqrt(n log)) ?
    Pvals = []
    for b in range(1, q):
        s = sum(u[t]*chibar(t, b) for t in perp_t)
        Pvals.append(abs(s))
    P = max(Pvals)
    Pmean = sum(v*v for v in Pvals)/len(Pvals)  # mean of |.|^2
    B = (math.sqrt(q)/m)*P
    Bdirect = max(abs(eta(b,G,psi,q)) for b in range(1,q))
    print(f"(C) P=max_b|sum u_t chibar(b)|={P:.4f}  (m={m}, sqrt(m)={math.sqrt(m):.3f}, sqrt(n*m)~{math.sqrt(n*m):.3f})")
    print(f"(C) B via (sqrt(q)/m)*P = {B:.4f}   B direct = {Bdirect:.4f}   |diff|={abs(B-Bdirect):.2e}")
    print(f"(C) P/sqrt(m)={P/math.sqrt(m):.4f}  P/sqrt(n)={P/math.sqrt(n):.4f}  E[|.|^2]={Pmean:.3f} (=n if random-flat over m freqs? expect ~?)")
    print(f"(C) B/sqrt(n)={Bdirect/math.sqrt(n):.4f}  B/sqrt(n*log2(m))={Bdirect/math.sqrt(n*math.log2(max(m,2))):.4f}")
    return Bdirect/math.sqrt(n*math.log2(max(m,2)))

if __name__ == "__main__":
    # proper-subgroup primes, n=2^mu << sqrt(q), exclude Fermat traps (need odd part of m > 1)
    cases = [
        (97, 8),     # m=12, sqrt(q)~9.8, n<sqrt q
        (193, 8),    # m=24
        (337, 16),   # m=21
        (1153, 16),  # m=72
        (3137, 16),  # m=196  q~ n^3
        (7681, 16),  # m=480
        (12289, 16), # m=768   (a known prize test prime)
        (12289, 32), # m=384
        (40961, 32), # m=1280
    ]
    for q, n in cases:
        if (q-1) % n != 0:
            print(f"skip q={q} n={n}: n does not divide q-1"); continue
        m = (q-1)//n
        # require odd part of m > 1 (avoid pure-2-power #400 trap)
        odd = m
        while odd % 2 == 0: odd//=2
        tag = "" if odd>1 else "  [WARN pure-2-power m: #400 trap]"
        run(q, n, rmax=4 if q < 5000 else 3)
        print(tag)
