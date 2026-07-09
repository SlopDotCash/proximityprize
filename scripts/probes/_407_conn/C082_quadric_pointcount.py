"""
C082 attack: Complement-quadric duality.
Claim: e2(A)=0  <=>  complement T satisfies S_T^2 = -Q_T  (S_T=sum g^i, Q_T=sum g^{2i}, i in T).
For top rows a = n-c (small c), |T|=c, the "bad-scalar count" is the F_q-rational
point count of an explicit c-variable quadric S^2 = -Q ON c-SUBSETS OF mu_n.
Connection asserts: this is a small-dimension quadric where Weil/Deligne is the RIGHT
tool, governed by classical quadratic-form theory => exact, q-independent delta* on top rows.

HONEST TEST (prize regime: proper dyadic subgroup mu_n, n=2^mu, q prime =1 mod n, q ~ n^beta):
  1. Verify the duality identity exactly at proper-subgroup primes.
  2. Count, for each c (size of complement T), the number of c-subsets T of mu_n with S_T^2 = -Q_T.
  3. Ask the decisive question: is this count predicted by classical full-field quadratic-form
     theory (q-independent, function of c and q only), OR does it depend on the SUBGROUP arithmetic
     (varies across primes with the SAME n, c)?  The latter = weld back to BGK/Paley.
"""
import itertools, sys

def is_prime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True

def find_subgroup_primes(n, count, beta_lo=4, beta_hi=6):
    """primes q = 1 mod n with q ~ n^beta, proper-subgroup regime (q >> n)."""
    out = []
    lo = max(n*n*4, n+1)        # ensure q >> n (proper subgroup, large prime)
    q = lo - (lo % n) + 1
    while len(out) < count:
        if q > 1 and is_prime(q) and q % n == 1:
            out.append(q)
        q += n
        if q > lo * 200: break
    return out

def primitive_nth_root(q, n):
    # find generator of mu_n: g with order exactly n
    for cand in range(2, q):
        # g = cand^((q-1)/n) is an n-th root; check order n
        g = pow(cand, (q-1)//n, q)
        if g == 1: continue
        # order divides n; check it's exactly n
        ok = True
        d = 1
        x = g
        order = 1
        # compute order by repeated mult (n small)
        y = g
        o = 1
        while y != 1:
            y = (y*g) % q
            o += 1
            if o > n: break
        if o == n:
            return g
    return None

def mu_n_elements(g, n, q):
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = (x*g) % q
    return out

def quadric_count_complement(g, n, q):
    """
    For each c = |T| from 1..min(n,5): count c-subsets T of mu_n (as a set of exponents)
    with (sum_{i in T} g^i)^2 == -(sum_{i in T} g^{2i})  mod q.
    Return dict c -> count.  These are the 'bad complements' for top row a=n-c.
    """
    elts = mu_n_elements(g, n, q)          # elts[i] = g^i
    sq   = [(e*e) % q for e in elts]        # g^{2i}
    idx = list(range(n))
    res = {}
    cmax = min(n, 5)
    for c in range(1, cmax+1):
        cnt = 0
        for T in itertools.combinations(idx, c):
            S = 0
            Q = 0
            for i in T:
                S = (S + elts[i]) % q
                Q = (Q + sq[i]) % q
            if (S*S) % q == (-Q) % q:
                cnt += 1
        res[c] = cnt
    return res

def verify_duality(g, n, q, ntests=8):
    """
    Check e2(A)=0 (i.e. sum over pairs i<j in A of g^{i+j} == 0)  <=>
    complement T = mu_n \ A satisfies S_T^2 = -Q_T.
    Test on random A (a few sizes near top, a = n-c).
    """
    elts = mu_n_elements(g, n, q)
    sq   = [(e*e) % q for e in elts]
    import random
    random.seed(1)
    allidx = set(range(n))
    fails = 0
    checks = 0
    for _ in range(ntests):
        c = random.randint(1, min(n-1, 4))
        T = set(random.sample(range(n), c))
        A = sorted(allidx - T)
        # e2(A) = sum_{i<j in A} g^{i+j}
        e2 = 0
        for ii in range(len(A)):
            for jj in range(ii+1, len(A)):
                e2 = (e2 + pow(g, A[ii]+A[jj], q)) % q
        lhs = (e2 == 0)
        # complement quadric
        S = sum(elts[i] for i in T) % q
        Qd = sum(sq[i] for i in T) % q
        rhs = ((S*S) % q == (-Qd) % q)
        checks += 1
        if lhs != rhs:
            fails += 1
    return checks, fails

def main():
    print("="*70)
    print("C082: complement-quadric duality + point-count subgroup-dependence test")
    print("="*70)
    for n in [8, 16, 32]:
        primes = find_subgroup_primes(n, 4)
        if len(primes) < 2:
            print(f"n={n}: not enough subgroup primes found"); continue
        print(f"\n### n = {n} (mu_n proper dyadic subgroup), beta=log_n(q):")
        counts_by_prime = []
        for q in primes:
            g = primitive_nth_root(q, n)
            if g is None:
                print(f"  q={q}: no primitive root?"); continue
            beta = (len(bin(q))-2)/ (len(bin(n))-2) if n>1 else 0
            import math
            beta = math.log(q)/math.log(n)
            checks, fails = verify_duality(g, n, q)
            cc = quadric_count_complement(g, n, q)
            counts_by_prime.append((q, cc))
            print(f"  q={q:>10}  beta={beta:4.2f}  duality {checks-fails}/{checks} OK  "
                  f"quadric-bad-count by c: {cc}")
        # decisive: do the counts AT THE SAME n,c vary across primes?
        if len(counts_by_prime) >= 2:
            print(f"  --> SUBGROUP-DEPENDENCE check (same n={n}, vary prime q):")
            for c in range(1, 6):
                vals = [cc.get(c) for (_q, cc) in counts_by_prime if c in cc]
                if not vals: continue
                same = len(set(vals)) == 1
                print(f"      c={c}: counts across primes = {vals}  "
                      f"{'CONSTANT (q-indep, classical-form-like)' if same else 'VARIES (subgroup-arithmetic dependent => BGK-like)'}")

if __name__ == "__main__":
    main()
