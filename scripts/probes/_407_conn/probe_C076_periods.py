"""
C076 probe step 1: compute exact Gaussian periods over a PROPER dyadic subgroup,
verify the even-moment (Bessel) law and the odd-moment law Sum eta^{2k+1} = -n^{2k},
and inspect the actual {eta_i} distribution: where is the max-atom, how does the
b=0 / full-group atom (eta_0 = n) sit relative to the off-diagonal spectrum.

Prize regime: n = 2^mu a PROPER subgroup of F_q*, q prime, q ~ n^beta, beta in 4..5.
We use exact integer/rational arithmetic via the cos representation of periods is
not exact; instead we work with the period values directly as algebraic integers by
grouping the coset sums of e_p(b*x). Since eta_b = sum_{x in mu_n} e_p(b*x) is generally
complex, but for the moment laws we use the REAL structure: actually periods are real
only when -1 in mu_n (n even => yes, n=2^mu has -1). For n=2^mu, mu_n is closed under
negation, so eta_b is real. Good.

We compute eta_b exactly as a sum of cos via high-precision, then ROUND, and verify
the integer moment laws.
"""
import cmath, math
from itertools import product

def primitive_root_subgroup(q, n):
    # find an element of order exactly n in F_q^*
    # q-1 divisible by n
    assert (q-1) % n == 0
    # find generator g of F_q^*, then g^((q-1)/n) has order n
    def order(a):
        o=1; x=a%q
        while x!=1:
            x=(x*a)%q; o+=1
        return o
    g=None
    for cand in range(2,q):
        if order(cand)==q-1:
            g=cand; break
    assert g is not None
    h=pow(g,(q-1)//n,q)  # order n
    sub=[]
    x=1
    for _ in range(n):
        sub.append(x); x=(x*h)%q
    assert len(set(sub))==n
    return sorted(set(sub)), g

def periods(q,n):
    sub,g=primitive_root_subgroup(q,n)
    m=(q-1)//n
    # coset reps of mu_n in F_q^*: powers g^0..g^{m-1}
    # eta for coset rep r: sum_{x in r*mu_n} e_p(x)  -- standard Gaussian period
    # But the connection's eta_b = sum_{y in mu_n} e_p(b*y); as b ranges over a coset
    # of mu_n this is constant. So distinct values = m periods indexed by cosets.
    cosets=[]
    seen=set()
    for j in range(m):
        r=pow(g,j,q)
        val=sum(cmath.exp(2*math.pi*1j*((r*y)%q)/q) for y in sub)
        cosets.append(val)
    # also the b=0 "atom": b=0 -> eta = sum_{y} e_p(0) = n. But b=0 is NOT a coset of mu_n
    # in F_q^*. The connection treats the FULL set over all b in F_q including 0?
    # Standard: periods are indexed by the m cosets of mu_n in F_q^* (b != 0).
    # The "full-group atom eta_0 = n" arises only if we include b=0.
    return cosets, m, sub

def check(q,n,maxk=4):
    cosets,m,sub=periods(q,n)
    realvals=[v.real for v in cosets]
    imagmax=max(abs(v.imag) for v in cosets)
    print(f"q={q} n={n} m={m}  max|imag|={imagmax if False else imagmax:.2e}" if False else f"q={q} n={n} m={m}  max|imag|={imagmax:.2e}".replace('imagmax',str(imagmax)))
    rounded=[round(v.real) for v in cosets]
    # moment laws over the m cosets (b != 0)
    print("  rounded period values (first 12):", rounded[:12])
    print("  min/max period:", min(rounded), max(rounded), " B=max|.|=", max(abs(x) for x in rounded))
    for k in range(0,maxk+1):
        # odd power sum 2k+1
        s_odd=sum(x**(2*k+1) for x in rounded)
        print(f"  k={k}: Sum eta^(2k+1)={s_odd}  (-n^{2*k}={-(n**(2*k))})  match={s_odd==-(n**(2*k))}")
    for r in range(1,maxk+1):
        s_even=sum(x**(2*r) for x in rounded)
        print(f"  r={r}: Sum eta^(2r)={s_even}")
    return rounded, m

if __name__=="__main__":
    imagmax=0
    # proper-subgroup, large-ish prime cases
    # n=8: need q prime, q=1 mod 8, q ~ n^beta. n^4=4096, n^5=32768
    for q,n in [(4099,8),(8089,8),(32833,8),(769,8),
                (4129,16),(8081,16),(65537,16),
                (8161,32),(32993,32),
                (8513,64),(65921,64)]:
        try:
            check(q,n)
        except AssertionError as e:
            print(f"q={q} n={n}: skip ({e})")
        print()
