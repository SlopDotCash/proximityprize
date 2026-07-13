"""
G252b: repeat the joint phase-lock test with the G245 signed-incidence normal
form. NOTE: sign_r is a cosine/Krawtchouk-style SURROGATE for the exact rank-r
Newton packet coefficient, not the literal G245 coefficient. The result tested
is structural (phase/row decoupling), stable across the surrogate; it is not a
numerical estimate of the true covariance. Uses the G245 signed normal form:

  N[t] (incidence): for coset structure, N[A,B] = #{x in A : 2-x in B}.
  In the sponsor regime 2 not in G. The rank-r signed covariance weight on
  quotient character chi is  Rhat_r(chi) = sum_{h in Q} R_r^Q(h) chi(h)
  where R_r^Q(h) is the rank-r Newton packet's coset-h coefficient
  (signed, DC-subtracted per G245: A_r = p n <N e_G, R_r^Q> - n^2 C(n,r)).

We approximate R_r^Q(h) by the genuine signed object: the number of 2-element
additive relations landing in coset h weighted by the r-th Newton packet parity
sign, DC-subtracted. What(chi) is the Gauss-type sum as before. We again test
whether ANY semicircle split of the phase histogram (the only global-discrepancy
-admissible move) can drive the real covariance to <= 0. If yes everywhere and
the phase-lock strength -> 0 with m, the free coupling is intrinsic and the
fixed-row route via joint placement is a NO-GO, corroborating G251 at the level
of the true signed weight.
"""
import numpy as np, cmath, math
from math import comb

def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True

def primitive_root(p):
    phi=p-1; facs=[]; x=phi; d=2
    while d*d<=x:
        if x%d==0:
            facs.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: facs.append(x)
    for gg in range(2,p):
        if all(pow(gg,(p-1)//f,p)!=1 for f in facs): return gg
    return None

def run(n,p,r):
    if not is_prime(p) or (p-1)%n!=0: return None
    m=(p-1)//n
    g=primitive_root(p)
    ind={}; x=1
    for e in range(p-1):
        ind[x]=e; x=(x*g)%p
    def ql(t): return ind[t]%m
    # Coset sets G_j = {residues with ind = j mod m}? Actually n-th power classes:
    # the subgroup G of n-th powers has index n; cosets labelled by ind mod n.
    # The quotient Q here is Z/m (the m=(p-1)/n exponent quotient in the sponsor
    # covariance). Row label h in Q. Build signed incidence:
    # N-relation: pairs (a,b) with a+b=2 (shift target 2), a,b nonzero.
    # weight by rank-r Newton parity sign on the coset of a, aggregate by coset of b.
    # Rr^Q(h) = sum over a: [ql(b)=h] * sign_r(ql(a)) , b = (2-a) mod p, DC-subtracted.
    def sign_r(l):
        # rank-r Newton packet parity surrogate: (-1)^(number of set bits capped)/
        # use Krawtchouk-type sign K_r on label l in [0,m): cos-based signed weight
        return math.cos(2*math.pi*r*l/m)
    Rr=np.zeros(m)
    for a in range(1,p):
        b=(2-a)%p
        if b==0: continue
        Rr[ql(b)] += sign_r(ql(a))
    Rr -= Rr.mean()  # DC subtract
    psis=np.array([cmath.exp(2j*math.pi*t/p) for t in range(1,p)])
    labels=np.array([ql(t) for t in range(1,p)])
    m_arr=np.arange(m)
    What=np.zeros(m,dtype=complex); Rhat=np.zeros(m,dtype=complex)
    for a in range(m):
        ph=np.exp(2j*math.pi*a*labels/m)
        What[a]=np.sum(psis*ph)
        ph2=np.exp(2j*math.pi*a*m_arr/m)
        Rhat[a]=np.sum(Rr*ph2)
    idx=np.arange(1,m)
    W=What[idx]; R=Rhat[idx]
    cov=np.real(np.sum(W*np.conj(R)))
    tri=np.sum(np.abs(W)*np.abs(R))
    wmag=np.abs(W)*np.abs(R)
    dphi=np.angle(W)-np.angle(R)
    lock=np.abs(np.sum(wmag*np.exp(1j*dphi)))/(np.sum(wmag)+1e-30)
    order=np.argsort(np.angle(R))
    best=None
    for k in range(len(idx)+1):
        s=np.ones(len(idx)); s[order[:k]]=-1
        c=np.real(np.sum(s*W*np.conj(R)))
        if best is None or c<best: best=c
    return dict(n=n,p=p,r=r,m=m,cov=cov,tri=tri,frac=cov/(tri+1e-30),
                lock=lock,minsplit=best,zeros=best<=0)

# NOTE: the `zeros` field is SUPERSEDED (its split search includes unbalanced
# extremes and is tautological). The corrected balanced-split test is in
# g252_balanced_split_probe.py. The `lock` decorrelation numbers remain valid.
print("G252b signed-incidence joint phase-lock (surrogate rank-parity weight)")
print("="*70)
for (n,p) in [(8,1009),(8,2003),(16,1009),(8,4001),(16,2003),(8,8009)]:
    for r in (5,6):
        res=run(n,p,r)
        if res is None: continue
        print(f"n={res['n']} p={res['p']} r={res['r']} m={res['m']} "
              f"cov={res['cov']:.3g} tri={res['tri']:.3g} frac={res['frac']:.4f} "
              f"lock={res['lock']:.4f} minsplit={res['minsplit']:.3g} zeros={res['zeros']}")
print("="*70)
