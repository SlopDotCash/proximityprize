"""
C092: Energy chain F5<->F2<->F18 via T(H) = #{(b,c) in H^2 : 1+b-c in H}.

Goal of attack (per attack_plan):
  - VERIFY the chain identities are exact at proper-subgroup PRIZE-REGIME primes:
       (a) E(H) = |H| * T(H)            [dilation reduction, EnergyDilationReduction]
       (b) q * E(H) = sum_b ||eta_b||^4 [fourth moment, SubgroupGaussSumFourthMoment]
       (c) |H| | E(H)                   [card_dvd_addEnergy]
  - TEST the attack_plan's quantitative hope: can T(H) be bounded ~ n^2/q so that
    E = |H|*T <= n^3/q (full-group Weil value) AND, crucially, hit the F2 target
    sqrt(n*polylog)?  Decompose:  E = n^2 (diagonal floor) + E_offdiag.
       random/Weil model: T(H) ~ n + n^2/q (the "+1" diagonal b=c plus n^2/q off).
    The deficit the attack_plan admits: E >= n^2 always so B = sup||eta_b|| satisfies
    only sqrt(nE/q-ish); the OPEN content is the OFF-DIAGONAL part of T.

We use EXACT integer arithmetic at multiple proper-subgroup large primes,
n = 8,16,32,64, q ~ n^beta (beta ~ 4-5), n << sqrt(q).
"""
import cmath, math

def find_subgroup(q, n):
    """H = unique subgroup of F_q^* of order n (q prime, n | q-1). Return sorted list."""
    g = primitive_root(q)
    # generator of order-n subgroup: g^((q-1)/n)
    h = pow(g, (q-1)//n, q)
    H = set()
    x = 1
    for _ in range(n):
        H.add(x)
        x = (x*h) % q
    assert len(H) == n, (q, n, len(H))
    return H

def primitive_root(p):
    if p == 2: return 1
    phi = p-1
    fac = factorize(phi)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no primroot")

def factorize(m):
    fac = set(); d=2
    while d*d <= m:
        while m % d == 0:
            fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    return fac

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def T_of_H(H, q):
    """T(H) = #{(b,c) in H^2 : 1+b-c in H}."""
    Hset = H
    t = 0
    for b in H:
        for c in H:
            v = (1 + b - c) % q
            if v in Hset:
                t += 1
    return t

def addEnergy(H, q):
    """E(H) = #{(a,a',c,c') in H^4 : a+a'=c+c'} via collision counting on sumset."""
    from collections import Counter
    cnt = Counter()
    for a in H:
        for ap in H:
            cnt[(a+ap) % q] += 1
    return sum(v*v for v in cnt.values())

def gauss_sum_4th_moment(H, q):
    """sum_{b in F_q} |eta_b|^4 where eta_b = sum_{y in H} exp(2pi i b y / q)."""
    Hl = list(H)
    total = 0.0
    for b in range(q):
        s = 0+0j
        for y in Hl:
            s += cmath.exp(2j*math.pi*(b*y % q)/q)
        total += abs(s)**4
    return total

def max_eta(H, q):
    Hl = list(H)
    best = 0.0
    for b in range(1, q):
        s = sum(cmath.exp(2j*math.pi*(b*y % q)/q) for y in Hl)
        best = max(best, abs(s))
    return best

# choose primes: q prime, q == 1 mod n, n proper subgroup (n < q-1), n << sqrt(q)
def find_prime(n, beta, count=2):
    target = int(round(n**beta))
    out=[]
    k = target // n
    while len(out) < count and k < target*8 + 10000:
        q = k*n + 1
        if q > n and is_prime(q) and (q-1) != n:  # proper subgroup
            # require n << sqrt(q): n^2 <= q  (Sidon window the chain uses)
            if n*n <= q:
                out.append(q)
        k += 1
    return out

print(f"{'n':>4} {'q':>9} {'q~n^':>6} {'T(H)':>8} {'E=|H|T?':>8} {'E_dir':>10} "
      f"{'qE=4thM?':>10} {'|H||E?':>7} {'T-n':>6} {'n^2/q':>8} {'(T-n)/(n^2/q)':>14} "
      f"{'B/sqrtn':>8} {'E/n^2':>8}")
for n in [8, 16, 32]:
    # for n=8,16 use exact gauss 4th moment (q small enough); n=32 skip 4thM (too big)
    for beta in [4.0, 5.0]:
        primes = find_prime(n, beta, count=1)
        for q in primes:
            H = find_subgroup(q, n)
            T = T_of_H(H, q)
            E = addEnergy(H, q)
            chain_a = (E == n*T)
            div_c = (E % n == 0)
            betahat = math.log(q)/math.log(n)
            do4 = (q <= 3000)  # exact complex 4th moment only for small q
            if do4:
                m4 = gauss_sum_4th_moment(H, q)
                chain_b = abs(m4 - q*E) < 1e-3 * max(1.0, q*E)
                B = max_eta(H, q)
                bratio = B/math.sqrt(n)
            else:
                chain_b = None
                bratio = float('nan')
            offdiag = T - n  # subtract diagonal b=c (always in H since 1+b-b=1 in H)
            n2q = n*n/q
            ratio = offdiag/n2q if n2q>0 else float('nan')
            print(f"{n:>4} {q:>9} {betahat:>6.2f} {T:>8} {str(chain_a):>8} {E:>10} "
                  f"{str(chain_b):>10} {str(div_c):>7} {offdiag:>6} {n2q:>8.3f} "
                  f"{ratio:>14.3f} {bratio:>8.3f} {E/n**2:>8.3f}")
