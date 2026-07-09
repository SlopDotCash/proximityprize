"""
C099 probe: Frobenius n|p+1 gives r(t)<=2 UNCONDITIONALLY (inert family).
Claim under attack: the COUNT FACE (rep count r(t)=#{y in mu_n : t-y in mu_n},
and the additive energy E_2 = sum_t r(t)^2) is provably O(1)/O(n) on the INERT
family n|p+1, isolating the wall to the SPLIT family n|p-1 (the prize regime).

We test, with EXACT integer arithmetic on PROPER subgroups mu_n = mu_{2^mu} of F_p*
(prize regime: n=2^mu << sqrt(p), q ~ n^beta, beta=4..5):

 (A) INERT family  n | p+1 : mu_n lives in F_{p^2} (NOT F_p). Compute r(t) and E_2
     for t ranging over the prime field F_p (the Frobenius-fixed elements, c^p=c).
     Lemma predicts max_t r(t) <= 2.

 (B) SPLIT family  n | p-1 : mu_n subset F_p (the PRIZE regime). Compute r(t),
     E_2 = sum_t r(t)^2, and the surplus over the inert baseline.

 (C) The lift test: does the attack_plan's "Frobenius-pairing the split sum with an
     inert one" / quadratic-extension transfer give ANY bound on the split E_2?
     We test whether the split count at a fixed t is controlled by an F_{p^2} object.

KEY structural fact to expose: the inert family is DISJOINT from the prize regime
(when n|p+1, n does NOT divide p-1 for n>2, so F_p* has NO order-n subgroup; there is
no smooth FFT domain over F_p). So "closing inert" closes a family the prize never uses.
"""
import sympy
from sympy import isprime, primitive_root, sqrt

def mu_n_in_Fp(p, n):
    """Return mu_n = {y in F_p* : y^n = 1} as a set (requires n | p-1)."""
    assert (p - 1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of order-n subgroup
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x * h) % p
    assert len(S) == n
    return S

def rep_count_split(p, n, S):
    """For each t in F_p, r(t) = #{y in S : (t - y) mod p in S}. Return dict and E_2."""
    Sset = S
    rs = {}
    for t in range(p):
        c = 0
        for y in Sset:
            if (t - y) % p in Sset:
                c += 1
        rs[t] = c
    E2 = sum(c * c for c in rs.values())
    return rs, E2

def mu_n_in_Fp2_inert(p, n):
    """n | p+1. Construct F_{p^2}=F_p[x]/(x^2 - d), d a nonresidue; return mu_n as
    list of (a,b) pairs (a + b*x). Frobenius is (a,b) -> (a, -b) (since x^p = -x when
    x^2 = d nonresidue, as d^((p-1)/2) = -1). mu_n: elements of multiplicative order
    dividing n. F_{p^2}* is cyclic of order p^2-1 = (p-1)(p+1); n | p+1 so mu_n exists."""
    assert (p + 1) % n == 0
    # find nonresidue d
    d = None
    for cand in range(2, p):
        if pow(cand, (p - 1) // 2, p) == p - 1:
            d = cand
            break
    assert d is not None
    # multiply in F_{p^2}: (a+bx)(c+ex) = (ac + be*d) + (ae+bc)x
    def mul(u, v):
        a, b = u; c, e = v
        return ((a * c + b * e * d) % p, (a * e + b * c) % p)
    def mpow(u, k):
        r = (1, 0)
        while k:
            if k & 1: r = mul(r, u)
            u = mul(u, u); k >>= 1
        return r
    # find generator g of F_{p^2}* of order p^2-1, then g^((p^2-1)/n) has order n
    order = p * p - 1
    # try random-ish generators
    for ga in range(2, p):
        for gb in range(1, p):
            g = (ga, gb)
            # check order = full (cheap-ish via factorization)
            ok = True
            for q in sympy.factorint(order):
                if mpow(g, order // q) == (1, 0):
                    ok = False; break
            if ok:
                gen = mpow(g, order // n)
                S = set()
                x = (1, 0)
                for _ in range(n):
                    S.add(x); x = mul(x, gen)
                assert len(S) == n, (len(S), n)
                return S, mul, d
    raise RuntimeError("no generator found")

def rep_count_inert_over_Fp(p, n):
    """n | p+1: mu_n subset F_{p^2}. For t in the PRIME FIELD F_p (Frobenius-fixed,
    embedded as (t,0)), r(t) = #{y in mu_n : (t,0)-y in mu_n}. Lemma: r(t)<=2."""
    S, mul, d = mu_n_in_Fp2_inert(p, n)
    def sub(u, v):
        a, b = u; c, e = v
        return ((a - c) % p, (b - e) % p)
    rs = {}
    for t in range(p):
        T = (t % p, 0)
        c = 0
        for y in S:
            if sub(T, y) in S:
                c += 1
        rs[t] = c
    # also over ALL of F_{p^2} (general c, not Frobenius-fixed) to test the
    # "for EVERY nonzero c" statement in the Lean lemma
    rs_all_max = 0
    for ta in range(p):
        for tb in range(p):
            T = (ta, tb)
            if T == (0, 0): continue
            c = 0
            for y in S:
                if sub(T, y) in S:
                    c += 1
            if c > rs_all_max: rs_all_max = c
    return rs, rs_all_max

# ---- find prize-regime primes ----
def find_split_primes(n, beta_lo, beta_hi, k=3):
    """primes p ~ n^beta with n | p-1, beta in [beta_lo, beta_hi]."""
    out = []
    lo = int(n ** beta_lo); hi = int(n ** beta_hi)
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while p <= hi and len(out) < k:
        if isprime(p) and p > n:
            out.append(p)
        p += n
    return out

def find_inert_primes(n, beta_lo, beta_hi, k=3):
    """primes p ~ n^beta with n | p+1 (so p = -1 mod n)."""
    out = []
    lo = int(n ** beta_lo); hi = int(n ** beta_hi)
    # p ≡ -1 mod n
    p = lo - (lo % n) - 1
    while p < lo: p += n
    while p <= hi and len(out) < k:
        if isprime(p) and p > n:
            out.append(p)
        p += n
    return out

print("="*78)
print("C099: rep-count r(t) and additive energy E_2 = sum r(t)^2")
print("INERT n|p+1 (Frobenius=inversion, NOT prize regime) vs SPLIT n|p-1 (PRIZE)")
print("="*78)

for n in [8, 16, 32]:
    mu = n.bit_length() - 1
    print(f"\n##### n = 2^{mu} = {n}   (proper dyadic subgroup) #####")

    # ---- SPLIT (prize regime): use modest beta so the brute force is feasible ----
    # For E_2 we must scan all t in F_p, so keep p small-ish. Use beta ~ 2.2..2.6
    # for the energy scan; ALSO show that the surplus law is the SAME object.
    sp = find_split_primes(n, 2.0, 2.7, k=3)
    print(f"  SPLIT primes (n|p-1): {sp}")
    for p in sp:
        S = mu_n_in_Fp(p, n)
        rs, E2 = rep_count_split(p, n, S)
        rmax = max(rs.values())
        # off-zero baseline: char-0 energy of mu_n is ~3n^2 (Lam-Leung). surplus:
        # the "diagonal" extra solutions are the char-p surplus ~ n^4/p (heuristic)
        surplus = E2 - (3 * n * n - 3 * n)  # vs char-0 even-n exact E_2 = 3n^2-3n
        print(f"    p={p:>7} (~n^{round(__import__('math').log(p)/__import__('math').log(n),2)}): "
              f"max_t r(t)={rmax:>3}, E_2={E2:>7}, "
              f"surplus(E_2 - charE2)={surplus:>6}, n^4/p={round(n**4/p,2)}")

    # ---- INERT (n|p+1): r(t) <= 2 claim ----
    ip = find_inert_primes(n, 2.0, 2.4, k=2)  # keep p small: F_{p^2} scan is p^2
    print(f"  INERT primes (n|p+1): {ip}")
    for p in ip:
        rs, rmax_all = rep_count_inert_over_Fp(p, n)
        rmax_fixed = max(rs.values())
        E2_fixed = sum(c*c for c in rs.values())
        print(f"    p={p:>7}: max_{{t in F_p}} r(t)={rmax_fixed} (Lemma<=2), "
              f"max_{{t in F_p^2*}} r(t)={rmax_all} (Lean claim<=2), "
              f"E_2 over F_p={E2_fixed}")
