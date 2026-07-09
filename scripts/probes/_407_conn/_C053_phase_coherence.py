"""
C053 sharpened probe (fast): the CRUX of the 'phase-only / amplitude-inert' claim.

Setup (exact at proper-subgroup primes, prize regime n=2^mu << sqrt(q)):
  eta_b = (sqrt(q)/m) * S(b),  S(b) := sum_{t in mu_n^perp} u_t * chibar_t(b),  |u_t|=1.
  So B := max_b |eta_b| = (sqrt(q)/m) * P,  P := max_b |S(b)|  (phase-only sum, all amps=1).

C053 says: the amplitude sqrt(q) is INERT and N0/B reduce to a moment of unit phases u_t over the
relation lattice => 'isolating the open core to phase-only'. We test what that buys:

  Q1 (identity): B == (sqrt(q)/m)*P exactly?            -> expect YES (algebra). Confirms (i)+(ii)+(iii).
  Q2 (does amplitude really drop out of the HARD object?):
       The conjectured house law is B ~ sqrt(n*log(m)). Via B=(sqrt(q)/m)P and q=n*m (since q-1=n*m):
          B ~ sqrt(n*m)/m * P = sqrt(n/m)*P  (approx). So B~sqrt(n log m)  <=>  P ~ sqrt(m log m).
       i.e. the phase-only sum P of m unit phases must itself exhibit sqrt(m log m) cancellation.
       Plot P/sqrt(m), P/sqrt(m log m). If P ~ m (no cancellation among phases) then B ~ sqrt(q)
       (trivial completion, NO prize). If P ~ sqrt(m log m) the prize is exactly the phase-coherence
       of {u_t}. -> tests whether 'phase-only' is a genuine simplification or just BGK re-dressed.
  Q3 (is {u_t} = Gauss phases the SAME object as BGK, or genuinely simpler?):
       Compare P (phase-only over Gauss phases u_t) to the cancellation of a RANDOM unit-phase family
       (i.i.d. uniform phases r_t): P_rand = max_b |sum r_t chibar(b)|. If P ~ P_rand, the Gauss
       phases are 'incoherent enough' empirically -- but that is precisely Katz/Rojas-Leon
       equidistribution = STILL the open BGK/Betti wall, not a closure.
"""
import cmath, math, random
from itertools import product

def primitive_root(q):
    phi=q-1; fac=set(); m=phi; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,phi//f,q)!=1 for f in fac): return g
    raise RuntimeError

def run(q,n,seed=0):
    assert (q-1)%n==0
    g=primitive_root(q); m=(q-1)//n
    # dlog table
    dlog={}; cur=1
    for e in range(q-1):
        dlog[cur]=e; cur=cur*g%q
    step=(q-1)//n
    G=[pow(g,step*k,q) for k in range(n)]
    twopi=2*math.pi
    psi=lambda x: cmath.exp(1j*twopi*(x%q)/q)
    w=twopi/(q-1)
    perp=[n*s for s in range(m)]
    # gauss sums tau(chi_t)
    taus={}
    for t in perp:
        s=0j
        for x in range(1,q):
            s+=cmath.exp(1j*w*t*dlog[x])*psi(x)
        taus[t]=s
    u={t: taus[t]/math.sqrt(q) for t in perp}
    # B direct
    def eta(b): return sum(psi(b*y%q) for y in G)
    Bdirect=max(abs(eta(b)) for b in range(1,q))
    # phase-only P
    def S(b): return sum(u[t]*cmath.exp(-1j*w*t*dlog[b]) for t in perp)
    Pvals=[abs(S(b)) for b in range(1,q)]
    P=max(Pvals)
    B_via=(math.sqrt(q)/m)*P
    # random unit-phase comparison
    random.seed(seed)
    rphase={t: cmath.exp(1j*twopi*random.random()) for t in perp}
    def Sr(b): return sum(rphase[t]*cmath.exp(-1j*w*t*dlog[b]) for t in perp)
    Prand=max(abs(Sr(b)) for b in range(1,q))
    sml=math.sqrt(m*math.log(max(m,2)))
    print(f"q={q:6d} n={n:3d} m={m:5d} | B={Bdirect:7.3f} B_via={B_via:7.3f} d={abs(Bdirect-B_via):.1e} "
          f"| P={P:7.2f} P/m={P/m:.3f} P/sqrt(m*lnm)={P/sml:.3f} "
          f"| Prand={Prand:7.2f} P/Prand={P/Prand:.3f} "
          f"| B/sqrt(n*log2 m)={Bdirect/math.sqrt(n*math.log2(max(m,2))):.3f}")

if __name__=="__main__":
    for q,n in [(97,8),(193,8),(337,16),(1153,16),(3137,16),(12289,16),(12289,32),(40961,32),(61441,32)]:
        if (q-1)%n: continue
        run(q,n)
