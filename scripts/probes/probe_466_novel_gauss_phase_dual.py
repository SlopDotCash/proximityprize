"""
N7-free lane probe: the Gauss-sum-phase / Stickelberger dual of M(n,p).

Verifies the load-bearing identity
    eta_b = (1/m) [ -1 + sum_{chi in H, chi != 1} conj(chi)(b) g(chi) ]
where H = characters of F_p^x trivial on mu_n (|H| = m = (p-1)/n), g(chi) the Gauss sum,
|g(chi)| = sqrt(p) exactly for chi != 1.

Then it tests the CRUX self-refutation claim: the magnitude data |g(chi)| = sqrt(p) is FLAT and
carries no information about max_b|eta_b|; the sup is decided by the PHASES arg g(chi). We test
this by re-randomizing the Gauss-sum phases (keeping |g|=sqrt p, and keeping the g(chi)g(chibar)=
chi(-1)p conjugate-pairing constraint) and checking the max_b|eta_b| stays at the same
sqrt(n log m) scale -- i.e. the true periods are NOT special among flat-magnitude phase choices,
so no magnitude/valuation-only argument can beat EVT.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for r in range(2, int(n**0.5)+1):
        if n % r == 0: return False
    return True

def primitive_root(p):
    # find generator of F_p^x
    fac = []
    phi = p-1
    d = 2; t = phi
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t//=d
        d+=1
    if t>1: fac.append(t)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    raise RuntimeError

def analyze(n, p, trials=200):
    assert (p-1) % n == 0
    m = (p-1)//n
    g = primitive_root(p)
    zeta_p = cmath.exp(2j*math.pi/p)
    # mu_n = <g^m>
    hm = pow(g, m, p)
    mu = [pow(hm, j, p) for j in range(n)]
    muset = set(mu)
    # eta_b directly
    def eta(b):
        return sum(zeta_p**((b*x) % p) for x in mu)
    etas = [eta(b) for b in range(1, p)]  # b != 0
    Ms = [abs(e) for e in etas]
    Mmax = max(Ms)
    # distinct values should be <= m
    distinct = len({round(e.real,6)+1j*round(e.imag,6) for e in etas})

    # characters trivial on mu_n: chi(g^k) = exp(2pi i * j * k / (p-1)) with chi trivial on mu_n
    # <=> chi(g^m)=1 <=> j*m/(p-1) integer <=> j multiple of n. So chi_t(g^k)=exp(2pi i * (t*n) * k/(p-1))
    #   = exp(2pi i * t * k / m), t = 0..m-1.  These are the m chars in H.
    # discrete log table
    dlog = {}
    acc = 1
    for k in range(p-1):
        dlog[acc] = k
        acc = (acc*g) % p
    def chi(t, x):  # x in F_p^x
        k = dlog[x % p]
        return cmath.exp(2j*math.pi * (t*k) / m)
    # Gauss sums g(chi_t) = sum_{y!=0} chi_t(y) e_p(y)
    G = []
    for t in range(m):
        s = sum(chi(t, y) * (zeta_p**(y % p)) for y in range(1, p))
        G.append(s)
    # check |g|=sqrt(p) for t!=0, g(chi_0) = -1
    absG = [abs(x) for x in G]
    magerr = max(abs(absG[t]-math.sqrt(p)) for t in range(1, m))

    # reconstruct eta_b via the identity and compare
    def eta_recon(b):
        s = -1.0 + 0j
        for t in range(1, m):
            # conj(chi_t)(b) = chi_t(b)^{-1}
            s += (1.0/chi(t, b)) * G[t]
        return s/m
    recon_err = max(abs(eta_recon(b) - eta(b)) for b in range(1, min(p, 40)))

    # CRUX: re-randomize phases of Gauss sums, keep |g|=sqrt p and conjugate pairing.
    # pairing: chi_t and chi_{m-t} are complex-conjugate characters; g(chi_t)g(chi_{-t}) = chi_t(-1) p.
    # arg g(chi_t)+arg g(chi_{-t}) = arg(chi_t(-1) p) = arg(chi_t(-1)) (0 or pi).
    def chi_at(t, x):
        k = dlog[x % p]
        return cmath.exp(2j*math.pi*(t*k)/m)
    rand_max = []
    for _ in range(trials):
        Gr = [None]*m
        Gr[0] = -1.0+0j
        for t in range(1, m):
            if Gr[t] is not None: continue
            tt = (m - t) % m
            pref = chi_at(t, p-1)  # chi_t(-1) = +-1
            ang = pref  # target product phase = chi_t(-1) (since p>0)
            theta = random.uniform(0, 2*math.pi)
            gt = math.sqrt(p)*cmath.exp(1j*theta)
            if tt == t:
                # self-paired (t = m/2): g^2 = chi(-1) p => g = sqrt(p)*sqrt(chi(-1))
                root = cmath.sqrt(ang)
                gt = math.sqrt(p)*root*(random.choice([1,-1]))
                Gr[t] = gt
            else:
                Gr[t] = gt
                Gr[tt] = (ang*p)/gt  # enforce product = chi_t(-1) p, |.|=sqrt p automatically
        # build etas from random phases
        def eta_r(b):
            s = -1.0+0j
            for t in range(1, m):
                s += (1.0/chi_at(t, b))*Gr[t]
            return s/m
        rmax = max(abs(eta_r(b)) for b in range(1, p))
        rand_max.append(rmax)
    rand_mean = sum(rand_max)/len(rand_max)
    scale = math.sqrt(n*math.log(m)) if m>1 else math.sqrt(n)

    print(f"n={n} p={p} m={m}:")
    print(f"  distinct eta values = {distinct} (<= m = {m})")
    print(f"  |g(chi)|=sqrt(p) max err (t!=0) = {magerr:.2e}   (sqrt p = {math.sqrt(p):.3f})")
    print(f"  identity reconstruction max err = {recon_err:.2e}")
    print(f"  TRUE   Mmax = {Mmax:.4f}   Mmax/sqrt(n log m) = {Mmax/scale:.4f}")
    print(f"  RANDOM-PHASE mean max = {rand_mean:.4f}   ratio = {rand_mean/scale:.4f}  "
          f"(min {min(rand_max):.3f} max {max(rand_max):.3f})")
    print(f"  => true-vs-random-phase max ratio = {Mmax/rand_mean:.4f}")
    print()
    return Mmax/scale, rand_mean/scale

random.seed(1)
cases = []
for p in range(17, 4000):
    if not is_prime(p): continue
    for mu_exp in (3,4,5):  # n = 8,16,32
        n = 2**mu_exp
        if (p-1) % n == 0 and (p-1)//n >= 3:
            cases.append((n,p))
# sample a spread
seen=set(); picked=[]
for n,p in cases:
    if n not in seen or len([1 for a,b in picked if a==n])<4:
        picked.append((n,p)); seen.add(n)
picked = sorted(set(picked))[:14]
tr=[]; rr=[]
for n,p in picked:
    a,b = analyze(n,p, trials=120)
    tr.append(a); rr.append(b)
print(f"TRUE   Mmax/sqrt(n log m): mean {sum(tr)/len(tr):.3f} range [{min(tr):.3f},{max(tr):.3f}]")
print(f"RANDOM Mmax/sqrt(n log m): mean {sum(rr)/len(rr):.3f} range [{min(rr):.3f},{max(rr):.3f}]")
