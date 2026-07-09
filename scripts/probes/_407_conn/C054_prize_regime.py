"""
C054 PRIZE REGIME (numpy-vectorized, feasible).
Family eta_b = sum_{y in mu_n} e_q(b*y), b in F_q*.  mu_n = proper dyadic subgroup, q ~ n^beta, large prime.

L2 mass is EXACT by Parseval: sum_{b in F_q} |eta_b|^2 = q*n  (indicator of mu_n, |mu_n|=n).
  => M := sum_{b!=0} = q*n - n^2 ;  avg over b!=0 = (q*n - n^2)/(q-1) ~ n.
We compute B^2 = max_{b!=0}|eta_b|^2 by vectorized scan.
"""
import math, numpy as np

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True

def find_prime(n, beta):
    target=int(round(n**beta))
    q=target - (target % n) + 1
    if q<=n: q+=n
    while not is_prime(q): q+=n
    return q

def subgroup_mu_n(q,n):
    assert (q-1)%n==0
    def order(a):
        o=1; x=a%q
        while x!=1:
            x=(x*a)%q; o+=1
        return o
    g=2
    while order(g)!=q-1: g+=1
    h=pow(g,(q-1)//n,q)
    mu=[]; x=1
    for _ in range(n):
        mu.append(x); x=(x*h)%q
    assert len(set(mu))==n
    return np.array(mu, dtype=np.int64)

def analyze(n,beta):
    q=find_prime(n,beta)
    mu=subgroup_mu_n(q,n)
    # B^2 = max over b in 1..q-1 of |sum_y e_q(b*y)|^2.  Vectorize over b in chunks.
    Mexact = q*n - n*n
    avg = Mexact/(q-1)
    best=0.0
    CH=2_000_00  # chunk of b values
    twopi_over_q = 2*math.pi/q
    b0=1
    while b0<q:
        b1=min(b0+CH,q)
        bs=np.arange(b0,b1,dtype=np.int64)
        # phases: outer (b * y) mod q  shape (len bs, n)
        ang = (np.outer(bs, mu) % q).astype(np.float64) * twopi_over_q
        re = np.cos(ang).sum(axis=1); im=np.sin(ang).sum(axis=1)
        mag2 = re*re+im*im
        m=mag2.max()
        if m>best: best=m
        b0=b1
    B=math.sqrt(best)
    print(f"n={n:5d} beta={beta} q={q:>14d}  q~n^{math.log(q)/math.log(n):.2f}")
    print(f"   avg_b|eta|^2={avg:.3f} (~n={n})   B^2={best:.3f}  B={B:.3f}")
    print(f"   TRUE gap max/avg              = {best/avg:.3f}")
    print(f"   claimed 'sqrt|V| tax'^2 = |V|=q = {q}")
    print(f"   B/sqrt(n)                     = {B/math.sqrt(n):.4f}  (2=Ramanujan)")
    print(f"   B/sqrt(n*log(q/n))            = {B/math.sqrt(n*math.log(q/n)):.4f} (BGK law)")
    print(f"   sqrt(q)/B (tax overshoot)     = {math.sqrt(q)/B:.1f}x", flush=True)

if __name__=="__main__":
    for n in [8,16,32,64,128,256,512]:
        analyze(n,4.5)
