"""
probe_444_padic_newton_spur_2adic_deep.py  (angle [padic-newton-spur], issue #444, DEEP)

Follow-up to probe_444_padic_newton_spur_2adic.py.  Two things to settle rigorously:

(A) CORRECTNESS of the carrier->cyclotomic map.  The first probe used the mu_n ELEMENTS'
    discrete-log INDICES as if mu_n[i] = zeta^i.  That is the RIGHT object: the abstract
    spur is a relation among the n-th ROOTS OF UNITY (a cyclotomic integer), and the F_p
    vanishing is the image under the fixed isomorphism mu_n(F_p) = <zeta_n> (zeta_n -> the
    generator g^{(p-1)/n}).  So the carrier alpha = sum eps_i zeta^{idx_i} is correct, and
    "p | N(alpha)" <=> "the relation vanishes in F_p at this embedding".  BUT we must verify
    that the spur carrier the energy count found actually DOES satisfy p | N(alpha) -- if the
    norm has v_p = 0, the carrier is NOT a genuine cyclotomic spur (it's a different-multiset
    coincidence that is NOT a single vanishing cyclotomic integer).  We re-extract carriers
    using the CYCLOTOMIC structure directly and check p | N.

(B) THE ACTUAL ANGLE QUESTION.  For the genuine cyclotomic spur carriers alpha (p | N(alpha),
    alpha != 0), tabulate v_2(N(alpha)) as a function of DEPTH r (weight 2r).  The angle asks:
    does the 2-adic valuation grow with r in a way that BOUNDS the deep-r spur (non-archimedean
    handle)?  Equivalently: is there a 2-adic lower bound on v_2 forcing |N| large (a Stickel-
    berger obstruction), OR is v_2 bounded/independent of p so the 2-part is a fixed factor
    that says NOTHING about which p divides N?

We do this by, for each (n, p), counting the genuine spur AND extracting ALL minimal carriers,
then reporting the distribution of v_2(N) and whether v_2 correlates with the F_p event.
"""
import math, itertools, cmath
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, lo):
    p = lo + ((1 - lo) % n)
    if p < lo: p += n
    while True:
        if is_prime(p): return p
        p += n

def subgroup_gen(p, n):
    g0 = 2
    while True:
        g = pow(g0, (p-1)//n, p)
        if len({pow(g, i, p) for i in range(n)}) == n:
            return g
        g0 += 1

def v2(x):
    if x == 0: return math.inf
    v = 0; x = abs(x)
    while x % 2 == 0: x //= 2; v += 1
    return v

def vp(x, p):
    if x == 0: return math.inf
    v = 0; x = abs(x)
    while x % p == 0: x //= p; v += 1
    return v

def factint(x):
    x = abs(x); f = Counter()
    d = 2
    while d*d <= x:
        while x % d == 0: f[d]+=1; x//=d
        d += 1 if d==2 else 2
    if x>1: f[x]+=1
    return dict(f)

def norm_cyclotomic(coeff, n):
    """N(alpha), alpha = sum coeff[k] zeta_n^k, reduced mod Phi_n(X)=X^{n/2}+1 (n=2^mu).
    Norm = prod over primitive n-th roots (odd t) of f(zeta^t)."""
    half = n//2
    N = 1.0+0j
    for t in range(1, n, 2):
        z = cmath.exp(2j*math.pi*t/n)
        val = sum(coeff[k]*z**k for k in range(half))
        N *= val
    return round(N.real)

def carrier_to_coeff(plus, minus, n):
    """plus, minus = lists of exponents in Z/n (indices of n-th roots). Reduce mod X^{n/2}+1."""
    half = n//2
    coeff = [0]*half
    def add(e, s):
        e %= n
        if e < half: coeff[e] += s
        else: coeff[e-half] -= s
    for e in plus: add(e, +1)
    for e in minus: add(e, -1)
    return coeff

def find_all_min_carriers(n, p, rmax, cap=40):
    """Genuine CYCLOTOMIC spur carriers: relations sum_{plus} zeta^{i} = sum_{minus} zeta^{j}
    in F_p (i.e. sum g^{i} == sum g^{j} mod p where g = generator of mu_n, zeta -> g) but with
    DIFFERENT multisets, at the minimal weight where any exist.  We verify p | N(alpha).
    Returns list of (r, plus, minus, N) up to cap, at the minimal r with carriers."""
    g = subgroup_gen(p, n)
    powg = [pow(g, i, p) for i in range(n)]   # g^i = the i-th root's F_p image
    for r in range(1, rmax+1):
        buckets = {}
        found = []
        for cp in itertools.combinations_with_replacement(range(n), r):
            s_mod = sum(powg[i] for i in cp) % p
            s_int = sum(powg[i] for i in cp)
            for (cm, sm_int) in buckets.get(s_mod, []):
                if cm != cp:
                    coeff = carrier_to_coeff(cp, cm, n)
                    if any(coeff):  # nonzero cyclotomic integer
                        N = norm_cyclotomic(coeff, n)
                        found.append((r, cp, cm, N))
                        if len(found) >= cap:
                            return found
            buckets.setdefault(s_mod, []).append((cp, s_int))
        if found:
            return found
    return []

print("="*88)
print("Genuine CYCLOTOMIC spur carriers: v_2(N) and v_p(N) at minimal depth r*")
print("="*88)
print("alpha = (sum of n-th roots) - (sum of n-th roots), DIFFERENT multisets, ==0 in F_p.")
print("p|N(alpha) is the F_p-vanishing event. v_2(N) is the 2-adic Stickelberger slot.")
print()
for n in [8, 16, 32]:
    for beta in [4]:
        p = find_prime(n, int(n**beta))
        rmax = 6 if n <= 16 else 5
        carriers = find_all_min_carriers(n, p, rmax, cap=60)
        if not carriers:
            print(f"n={n} p={p}: no cyclotomic carrier in range r<={rmax}")
            continue
        r0 = carriers[0][0]
        v2s = [v2(N) for (_,_,_,N) in carriers if N != 0]
        vps = [vp(N, p) for (_,_,_,N) in carriers if N != 0]
        n_pdiv = sum(1 for x in vps if x >= 1)
        n_zeroN = sum(1 for (_,_,_,N) in carriers if N == 0)
        print(f"n={n:>3} p={p:>9} beta={beta}  r*={r0}  weight={2*r0}  #carriers={len(carriers)}")
        print(f"    N==0 (char-0 vanisher, NOT a spur): {n_zeroN}/{len(carriers)}")
        print(f"    N!=0 & p|N (GENUINE spur):           {n_pdiv}/{len(v2s)}")
        if v2s:
            print(f"    v_2(N) distribution: {dict(Counter(v2s))}   (min={min(v2s)}, max={max(v2s)})")
            print(f"    v_p(N) distribution: {dict(Counter(vps))}")
        # show a few example factorizations
        shown = 0
        for (r, cp, cm, N) in carriers:
            if N != 0 and vp(N,p) >= 1:
                print(f"      GENUINE: plus={cp} minus={cm}  N={N}  = {factint(N)}")
                shown += 1
                if shown >= 3: break
        if shown == 0:
            # show that the 'spur' from energy count is NOT a single cyclotomic vanisher
            for (r, cp, cm, N) in carriers[:3]:
                print(f"      (not p|N): plus={cp} minus={cm}  N={N}  v2={v2(N)} vp={vp(N,p)}  = {factint(N) if N!=0 else '0'}")
        print()

print("="*88)
print("VERDICT LOGIC")
print("="*88)
print("If genuine cyclotomic carriers (p|N) exist and v_2(N) is BOUNDED / does not grow with r,")
print("the 2-adic part is a p-independent bounded factor (Stickelberger digit sums give a FIXED")
print("2-power), so v_2 cannot detect WHICH p divides N => non-archimedean handle is wrong-norm")
print("=> reduces to wall (B2). If the energy-count 'spur' carriers have v_p=0 (p does NOT divide")
print("the cyclotomic norm), then the additive-energy defect is NOT a single cyclotomic vanishing")
print("at all -- it is a MULTISET coincidence of FIELD elements (sum of g^i mod p), and the")
print("cyclotomic/2-adic norm object is simply the WRONG object for it (B3: hypothesis fails on")
print("the flat structure).")
