"""
C062: "Stepanov gives a FIXED-r theorem the Weil/AG route cannot."

CLAIM under attack (attack_plan): there is an order-3 confluent auxiliary Psi
vanishing to order >=3 at every y in A = mu_n cap (c + mu_n), with deg Psi ~ n
(more precisely the attack hopes deg Psi = O(n + M^2) for an order-M family,
which optimized over M gives r(c) <= O(n^{2/3}), E_p <= O(n^{8/3})).

We test the EXISTENCE and the DEGREE of the minimal-degree auxiliary vanishing to
order M on A, exactly, over a PRIZE-regime proper-subgroup prime field F_p with
mu_n a thin dyadic subgroup (n = 2^mu | p-1, n << sqrt(p)).

Method (exact linear algebra over F_p):
  - The set of polynomials of degree <= D vanishing to order >= M at each y in A
    is the kernel of the |A|*M  x  (D+1) "confluent Vandermonde / Hasse-derivative"
    matrix H, whose rows are the Hasse derivatives D^{(j)}(X^i) evaluated at y,
    for y in A, j=0..M-1, i=0..D.
  - A nonzero auxiliary of degree <= D exists  <=>  rank(H) < D+1.
  - The MINIMAL degree d_min(M) of a nonzero order-M auxiliary is the smallest D
    with rank(H_D) < D+1, i.e. the smallest D with (D+1) > rank(H_D).
  - Stepanov then gives  r(c) * M <= deg Psi = d_min(M),  i.e. r(c) <= d_min(M)/M.

KEY QUESTION: does d_min(M) stay ~ c*n (so r(c) <= ~ c*n/M improves with M),
or does d_min(M) grow like M*|A| (generic, giving r(c) <= |A| ~ n/2, NO gain)?

If d_min(M) ~ M*|A|, the confluent route is the GENERIC dimension count in disguise
(StepanovGenericInsufficiency) and gives NO sub-(n/2) bound -> connection refuted/open.
If d_min(M) ~ const*n independent of M, the route works -> connection lives.

We compute d_min(M) exactly for M = 1,2,3,4,5,... at several (n, p, c).
"""

import sys

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def find_prize_prime(n, beta_min):
    # p prime, p == 1 mod n, p ~ n^beta with beta>=beta_min, n a PROPER subgroup (n != p-1).
    target = max(n**beta_min, 3*n)
    # round target up to == 1 mod n
    k = (target - 1)//n + 1
    while True:
        p = k*n + 1
        if is_prime(p):
            return p
        k += 1

def find_root_of_unity(p, n):
    # find a generator g of F_p*, then g^((p-1)/n) has order n.
    # find primitive root
    from sympy import primitive_root  # not guaranteed; fallback below
    return primitive_root(p)

def primitive_root_manual(p):
    # factor p-1
    m = p-1
    fac = set()
    d = 2
    mm = m
    while d*d <= mm:
        while mm % d == 0:
            fac.add(d); mm//=d
        d += 1
    if mm>1: fac.add(mm)
    for g in range(2, p):
        if all(pow(g, m//q, p) != 1 for q in fac):
            return g
    return None

def mu_n(p, n):
    g = primitive_root_manual(p)
    w = pow(g, (p-1)//n, p)  # primitive n-th root
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = (x*w) % p
    assert len(S) == n
    return S

def hasse_coeff(i, j, p):
    # Hasse derivative D^{(j)} X^i = C(i,j) X^{i-j}; we need binom(i,j) mod p and exponent i-j.
    # returns (binom(i,j) mod p, i-j) or None if i<j
    if i < j: return None
    # binom(i,j) mod p via Lucas (p large enough that i<p typically, but be safe)
    return (binom_mod(i, j, p), i - j)

def binom_mod(i, j, p):
    # i,j < p in all our uses (D < p). compute directly.
    if j < 0 or j > i: return 0
    num = 1; den = 1
    for t in range(j):
        num = (num * ((i - t) % p)) % p
        den = (den * ((t + 1) % p)) % p
    return (num * pow(den, p-2, p)) % p

def rank_mod_p(rows, ncols, p):
    # Gaussian elimination over F_p. rows: list of lists length ncols.
    mat = [r[:] for r in rows]
    rank = 0
    col = 0
    nrows = len(mat)
    pivot_row = 0
    for col in range(ncols):
        # find pivot
        piv = None
        for r in range(pivot_row, nrows):
            if mat[r][col] % p != 0:
                piv = r; break
        if piv is None:
            continue
        mat[pivot_row], mat[piv] = mat[piv], mat[pivot_row]
        inv = pow(mat[pivot_row][col], p-2, p)
        mat[pivot_row] = [(v*inv) % p for v in mat[pivot_row]]
        for r in range(nrows):
            if r != pivot_row and mat[r][col] % p != 0:
                f = mat[r][col]
                mat[r] = [(mat[r][k] - f*mat[pivot_row][k]) % p for k in range(ncols)]
        pivot_row += 1
        rank += 1
        if pivot_row == nrows: break
    return rank

def build_H(A, M, D, p):
    # rows: for each y in A, for j in 0..M-1: row over columns i=0..D of Hasse coeff.
    rows = []
    ncols = D+1
    for y in A:
        # precompute powers of y up to D
        powy = [1]*(D+1)
        for i in range(1, D+1):
            powy[i] = (powy[i-1]*y) % p
        for j in range(M):
            row = [0]*ncols
            for i in range(j, D+1):
                b = binom_mod(i, j, p)
                if b == 0:
                    continue
                row[i] = (b * powy[i-j]) % p
            rows.append(row)
    return rows, ncols

def d_min(A, M, p, Dmax):
    # smallest D with a nonzero deg<=D poly vanishing to order >=M on A.
    # equivalently rank(H_D) < D+1.
    for D in range(0, Dmax+1):
        rows, ncols = build_H(A, M, D, p)
        rk = rank_mod_p(rows, ncols, p)
        if rk < ncols:
            return D
    return None

def repcount(S, c, p):
    # r(c) = #{ y in S : (c - y) mod p in S }   (number of representations / reps of c as sum a+b? )
    # Here repCount G c = |{y in G : c - y in G}| matching the Lean def (filter c - y in G).
    return sum(1 for y in S if ((c - y) % p) in S)

def run(n, beta_min):
    p = find_prize_prime(n, beta_min)
    S = mu_n(p, n)
    print(f"\n=== n={n} (2^{n.bit_length()-1}), p={p} ~ n^{round(__import__('math').log(p, n),2)} "
          f"(proper subgroup: n={n} != p-1={p-1})  [n/sqrt(p)={n/p**0.5:.4f}] ===")
    # pick an OFF-DIAGONAL c: c != 0, c^n != 1  -> c not in mu_n  -> A = mu_n cap (c+mu_n) is the degenerate set
    # find such c, and compute A.
    import random
    random.seed(1)
    for trial in range(2):
        # pick c with c not in S (off-diagonal coset) and |A| reasonably large
        best = None
        for _ in range(400):
            c = random.randrange(1, p)
            if c in S:   # c^n == 1
                continue
            A = [y for y in S if ((c - y) % p) in S]
            if len(A) >= 3:
                best = (c, A);
                if len(A) >= max(2, n//8): break
        if best is None:
            print("  (no off-diagonal c with |A|>=3 found at this n)"); return
        c, A = best
        rc = repcount(S, c, p)
        assert rc == len(A)
        print(f"  off-diag c={c}, |A| = r(c) = {len(A)}   (trivial bound r<= n={n}; order-2 bound r<=(n+1)/2={ (n+1)//2 })")
        # cap degree search: generic worst case is M*|A|; cap a bit above to see the trend
        Dmax = min(M_max_for*(len(A)) + 4, 3*n + 8)
        print(f"   M :  d_min(M)   r-bound=floor(d_min/M)   d_min/|A|   d_min/(M*|A|)")
        for M in range(1, M_max_for+1):
            dm = d_min(A, M, p, Dmax)
            if dm is None:
                print(f"   {M} :  >Dmax({Dmax})  (no aux of degree<=Dmax)")
                continue
            rbound = dm // M
            print(f"   {M} :   {dm:5d}      {rbound:5d}            {dm/len(A):6.3f}      {dm/(M*len(A)):6.3f}")
        break

if __name__ == "__main__":
    M_max_for = 5
    for n in (8, 16, 32):
        run(n, beta_min=4)
