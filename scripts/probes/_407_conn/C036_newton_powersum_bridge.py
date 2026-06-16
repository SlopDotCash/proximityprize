"""
C036 probe: Vieta-pin makes COUNT face a power-sum-Newton image (F3<->F5 bridge).

Claim under attack (from C036.json):
  lacBad(mu_n, a, t) = { e_t(S) : S subset mu_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 }, t=a-b.
  By Newton's identities, {e_1=...=e_{t-1}=0} <=> {p_1=...=p_{t-1}=0} (power sums),
  with then p_t = (-1)^{t-1} t e_t.
  This makes #lacBad literally a vanishing-power-sum subset count = the additive-energy/
  moment object F5/F13 that EnergyRelationAntipodal/LamLeung control in char 0 --- a
  char-sum-FREE bridge from F3 (count) to F5 (energy).

Tests, all exact-integer arithmetic, at PROPER dyadic subgroups mu_n < F_q^*, n=2^mu,
q prime = 1 mod n, q ~ n^beta (beta >= 4), n << sqrt(q):
  (T1) Newton-identity equivalence: {e_1=...=e_{t-1}=0} == {p_1=...=p_{t-1}=0} exactly
       (over F_q, where t-1 < char so the t! is invertible). And p_t = (-1)^{t-1} t e_t.
  (T2) #lacBad and #vanishingVariety at the cleanest radius delta = 1 - a/n.
       Is #lacBad O(n)? Is it a union of <g^t>-cosets (the coset-quantization claim)?
  (T3) The decisive WALL test: is the count GOVERNED by the same energy quantity, i.e.
       does the vanishing-power-sum subset count reproduce the additive-energy object the
       BGK/Lam-Leung wall blocks --- or is it an independent handle?
       We compare #vanishingVariety against the energy E_{t-1}(mu_n) (the deep-moment object).
"""
import itertools, sys
from math import comb

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_q(n, beta_min=4, count=2):
    """primes q = 1 mod n, q ~ n^beta, beta>=beta_min, proper subgroup mu_n."""
    out=[]
    target = n**beta_min
    k = target // n
    while len(out) < count:
        q = k*n + 1
        if q > n*target*64:  # cap
            break
        if is_prime(q):
            out.append(q)
        k += 1
    return out

def subgroup(n, q):
    """mu_n = the n-th roots of unity in F_q (n | q-1). Return sorted list."""
    # find a generator of F_q^*, then g^((q-1)/n)
    # crude: find primitive root
    def order(a):
        o=1; x=a
        while x!=1:
            x=x*a%q; o+=1
        return o
    g=None
    for cand in range(2,q):
        if pow(cand, (q-1)//2, q)!=1:  # quick nonresidue filter
            # verify primitive
            if order(cand)==q-1:
                g=cand; break
    h = pow(g, (q-1)//n, q)
    S=set(); x=1
    for _ in range(n):
        S.add(x); x=x*h%q
    assert len(S)==n
    return sorted(S), h, g

def esymm_mod(T, t, q):
    """e_t of a tuple T of field elements, mod q."""
    # e_t = sum over t-subsets of product
    if t==0: return 1%q
    if t>len(T): return 0
    s=0
    for sub in itertools.combinations(T, t):
        p=1
        for x in sub: p=p*x%q
        s=(s+p)%q
    return s

def psum_mod(T, j, q):
    return sum(pow(x, j, q) for x in T) % q

def run(n, beta_min=4):
    qs = find_q(n, beta_min, count=2)
    if not qs:
        print(f"  n={n}: no prime found"); return
    print(f"n={n}=2^{n.bit_length()-1}, candidate primes (q~n^{beta_min}+): {qs}")
    for q in qs[:1]:
        S, h, g = subgroup(n, q)
        beta = (q).bit_length()/ (n.bit_length()-1 if n>1 else 1)
        print(f"  q={q}  (q ~ n^{round(__import__('math').log(q,n),2)}), mu_n built (gen h={h})")
        # window-interior gaps t; cleanest radius delta = 1 - a/n with a = small.
        # prize window: rate rho ~ small; pick a = t+1 .. modest, gap t modest, |S|=a small
        # to keep brute force feasible we use small a.
        for a in range(2, min(n, 7)):
            for t in range(2, a+1):  # gap t = a - b, b = a - t >= 0
                if t-1 >= q: continue
                # T1: Newton equivalence  &  p_t = (-1)^{t-1} t e_t on the vanishing set
                # T2: enumerate vanishingVariety by e-constraints; by p-constraints; compare
                bad_e=set(); var_e=0
                bad_p=set(); var_p=0
                newton_pt_ok=True
                for sub in itertools.combinations(S, a):
                    e_van = all(esymm_mod(sub, j, q)==0 for j in range(1,t))
                    p_van = all(psum_mod(sub, j, q)==0 for j in range(1,t))
                    if e_van:
                        var_e+=1
                        bad_e.add(esymm_mod(sub, t, q))
                        # check p_t = (-1)^{t-1} t e_t
                        et=esymm_mod(sub,t,q); pt=psum_mod(sub,t,q)
                        rhs=((-1)**(t-1) * t * et) % q
                        if pt%q != rhs%q:
                            newton_pt_ok=False
                    if p_van:
                        var_p+=1
                        bad_p.add(esymm_mod(sub, t, q))
                if var_e==0 and var_p==0:
                    continue
                equiv = (var_e==var_p) and (bad_e==bad_p)
                # coset structure of lacBad under multiplication by h^t (g=h, h^t generates <h^t>)
                gt = pow(h, t, q)
                ord_gt = n // __import__('math').gcd(t, n)
                coset_closed = all((x*gt%q) in bad_e for x in bad_e) if bad_e else True
                ncos = len(bad_e)
                tag = "EQUIV" if equiv else "**MISMATCH**"
                ptag = "p_t=ID-OK" if newton_pt_ok else "**p_t-FAIL**"
                ccos = "coset-closed" if coset_closed else "**not-closed**"
                print(f"    a={a} t={t} b={a-t}: #var(e)={var_e} #var(p)={var_p} {tag}; "
                      f"#lacBad={ncos} (mult of ord(g^t)={ord_gt}? {ncos%ord_gt==0}) {ccos}; "
                      f"O(n)? {ncos}<= ~n={n}; {ptag}")

if __name__=="__main__":
    for n in (8, 16, 32):
        run(n, beta_min=4)
        print()
