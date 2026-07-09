#!/usr/bin/env python3
"""
I031 increment probe — does |eta_b - eta_c| have a DETERMINISTIC sub-Gaussian
tail in the QUOTIENT metric d_q(b,c)?  (Issue #444, lead I031.)

SETUP.  p prime, p-1 = m*n, mu_n = order-n subgroup of F_p^x (PROPER, index m).
Gauss period eta_b = sum_{x in mu_n} e_p(b x).  eta_b is constant on cosets b*mu_n,
so there are m distinct periods eta_c, c=0..m-1, indexed by the quotient Q=F_p^x/mu_n
(itself cyclic of order m, generator = g*mu_n with g a primitive root).

I031 CLAIM (group-invariant Dudley chaining on the quotient).  Because the index set
is the quotient Q (size m, not p), chaining collapses metric entropy to log m, and the
floor B = max_c|eta_c| <= C sqrt(n log m) would follow from a DETERMINISTIC increment
estimate: |eta_b - eta_c| is sub-Gaussian in a quotient metric d_q(b,c).

THE INCREMENT.  eta_b - eta_c = sum_x e_p(c x)(e_p((b-c)x) - 1).  We test several
candidate quotient metrics d_q and ask: is there a deterministic bound
        |eta_b - eta_c|  <=  K * d_q(b,c)        (Lipschitz)   OR
        #{(b,c): |eta_b - eta_c| > t} <= m^2 exp(-t^2 / (2 D)) (sub-Gaussian increment)
with D = O(n)?  Three outcomes to distinguish:
  (a) ELEMENTARY: increment is Lipschitz / controlled by char-sum manipulation -> I031 closes.
  (b) WALL: the increment is ITSELF a worst-case incomplete char sum (a Gauss period of a
      RELATED subgroup), so sup over increments ~ B again -> reduces to wall.
  (c) EASIER: increment has strictly MORE cancellation than B -> genuinely easier.

KEY DIAGNOSTICS.
 1. d2_min: is the L2 increment ever ~0 between DISTINCT cosets?  If yes, NO metric that is
    bounded-below away from 0 on distinct cosets can be sub-Gaussian -> chaining setup is
    *vacuous* unless the metric itself collapses (i.e. d_q does not separate the periods).
 2. Algebraic identity: eta_b - eta_c = eta'_{?}  -- is the increment a Gauss period of a
    different subgroup / a complete char sum?  We test |eta_b - eta_0| against the period of
    mu_n at frequency-difference and against the "doubled" object.
 3. max increment vs B: is sup_{b,c}|eta_b-eta_c| ~ 2B (wall) or o(B) (easier)?
 4. Lipschitz test: best K with |eta_b-eta_c| <= K*d_q for the natural quotient distance
    d_q(b,c) = min additive |k| with c = b*g^k (cyclic-quotient graph distance).  If K must
    GROW with m, increment is NOT Lipschitz in the quotient metric (chaining fails this route).
"""
import cmath, math

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac=[]; t=phi; d=2
    while d*d <= t:
        if t%d==0:
            fac.append(d)
            while t%d==0: t//=d
        d+=1
    if t>1: fac.append(t)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def gauss_periods(p, n, g=None):
    """eta indexed by quotient: eta[c] = period of coset g^c * mu_n, c=0..m-1."""
    assert (p-1)%n==0
    m=(p-1)//n
    if g is None: g=primitive_root(p)
    gen=pow(g,m,p)
    mu=[]; x=1
    for _ in range(n): mu.append(x); x=(x*gen)%p
    e=[cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas=[]; bc=1
    for c in range(m):
        s=0j
        for x in mu: s+=e[(bc*x)%p]
        etas.append(s); bc=(bc*g)%p
    return etas,m,g

def quotient_circular_dist(c, cp, m):
    """Natural cyclic-quotient graph distance: min |k| s.t. cp = c + k (mod m)."""
    d = abs(c-cp) % m
    return min(d, m-d)

def analyze(p, n):
    etas, m, g = gauss_periods(p, n)
    # 1. increment magnitudes over all distinct pairs
    incs = []          # (|eta_c - eta_cp|, quotient_dist)
    for i in range(m):
        for j in range(i+1, m):
            incs.append((abs(etas[i]-etas[j]), quotient_circular_dist(i,j,m)))
    mags = [a for a,_ in incs]
    B = max(abs(e) for e in etas)
    maxinc = max(mags)
    mininc = min(mags)
    # 2. nearest-neighbor increment (quotient dist = 1): is it ~ const (Lipschitz step)?
    nn = [a for a,d in incs if d==1]
    nn_mean = sum(nn)/len(nn) if nn else float('nan')
    nn_max = max(nn) if nn else float('nan')
    # 3. Lipschitz constant per unit quotient distance: K = max over pairs of |inc|/d_q
    K = max(a/d for a,d in incs if d>0)
    # the increment at quotient-dist 1 SHOULD already be ~sqrt(2n) if metric is flat;
    # the ratio nn_max / sqrt(2n) tells whether a single quotient step is a full sqrt(2n) jump.
    sqrt2n = math.sqrt(2*n)
    # 4. min increment between distinct cosets -- does the metric separate periods?
    return dict(p=p,n=n,m=m,g=g,B=B,maxinc=maxinc,mininc=mininc,
               nn_mean=nn_mean,nn_max=nn_max,K=K,sqrt2n=sqrt2n,
               maxinc_over_2B=maxinc/(2*B), mininc_over_sqrt2n=mininc/sqrt2n,
               nn_max_over_sqrt2n=nn_max/sqrt2n)

def algebraic_increment_test(p, n):
    """Is eta_b - eta_c expressible as a single subgroup character sum (wall) or does it
    have extra structure?  We test the specific increment eta_{g}- eta_{1} (quotient step 1):
        eta_g - eta_1 = sum_{x in mu} (e_p(g x) - e_p(x)) = sum_{x in mu} e_p(x)(e_p((g-1)x)-1).
    Compare |eta_g - eta_1| to the period at frequency (g-1) of mu_n -- if they coincide in
    magnitude, the increment IS a Gauss period (wall). Also report whether the SET of all
    increments {eta_b - eta_c} as a multiset has the same sup-scaling as {eta_b} (wall) or
    is uniformly smaller (easier)."""
    etas,m,g=gauss_periods(p,n)
    # period at frequency f: eta_f directly (already coset-indexed) -- but (g-1) lands in some
    # coset; the increment is NOT a single period, it's a difference. Test the "wall" hypothesis
    # by: is max_{b,c}|eta_b-eta_c| asymptotic to 2*max|eta_b| (i.e. attained near antipodal)?
    B=max(abs(e) for e in etas)
    # increment as its own "period family": define delta_k(c) = eta_{c+k}-eta_c (fixed shift k).
    # For each shift k, max_c|delta_k(c)| is a sup over m values. The WALL hypothesis says
    # max over BOTH k and c ~ 2B. The EASIER hypothesis says for SMALL k it is o(B).
    shift_sup = {}
    for k in range(1, min(m,9)):
        s = max(abs(etas[(c+k)%m]-etas[c]) for c in range(m))
        shift_sup[k]=s
    return B, shift_sup

def main():
    print("=== I031 INCREMENT PROBE: deterministic sub-Gaussian tail in quotient metric? ===\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'B':>7} {'maxInc':>7} {'mxI/2B':>7} {'minInc':>7} "
          f"{'mnI/√2n':>8} | {'nnMean':>7} {'nnMax':>7} {'nnMx/√2n':>8} | {'K(Lip)':>7}")
    cases=[]
    for n in [32,64,128]:
        cnt=0; p=n+1
        while cnt<5:
            p+=n
            if is_prime(p) and (p-1)%n==0:
                m=(p-1)//n
                if m<8: continue
                if p>40000: break
                cases.append((p,n)); cnt+=1
    for (p,n) in cases:
        r=analyze(p,n)
        print(f"{r['p']:>7} {r['n']:>4} {r['m']:>5} | {r['B']:7.3f} {r['maxinc']:7.3f} "
              f"{r['maxinc_over_2B']:7.3f} {r['mininc']:7.3f} {r['mininc_over_sqrt2n']:8.3f} | "
              f"{r['nn_mean']:7.3f} {r['nn_max']:7.3f} {r['nn_max_over_sqrt2n']:8.3f} | {r['K']:7.3f}")

    print("\n=== SHIFT-SUP test: max_c|eta_{c+k}-eta_c| vs B (wall if ~2B already at small k) ===")
    print("(if shift-sup ~ 2B for ALL k>=1 incl k=1, increment IS the wall; if grows with k, easier)\n")
    for (p,n) in [(257,16),(577,32),(1153,64),(2129,128) if is_prime(2129) else (1153,64)]:
        if (p-1)%n!=0 or not is_prime(p): continue
        B, ss = algebraic_increment_test(p,n)
        row=" ".join(f"k={k}:{v/B:.2f}B" for k,v in ss.items())
        print(f"p={p:>6} n={n:>4} m={(p-1)//n:>4} B={B:6.3f} | shift-sup/B: {row}")

    print("\n=== INTERPRETATION KEYS ===")
    print("minInc/√2n ~ 0  => DISTINCT cosets have near-equal periods: no quotient metric")
    print("                   bounded-below on distinct cosets is sub-Gaussian => Dudley vacuous")
    print("                   UNLESS d_q itself collapses (metric must IGNORE quotient position).")
    print("nnMax/√2n ~ 1   => a SINGLE quotient step is already a full sqrt(2n) jump =>")
    print("                   increment NOT Lipschitz in cyclic-quotient distance.")
    print("maxInc/2B ~ 1   => sup increment ~ 2B (attained antipodally) => increment sup = WALL.")

if __name__=="__main__":
    main()
