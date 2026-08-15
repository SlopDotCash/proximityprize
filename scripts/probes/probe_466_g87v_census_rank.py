#!/usr/bin/env python3
"""
[466-G87V follow-up] Census-rank probe: is the support-six census at a fixed degree-one
prime ever FULL RANK (the hypothesis censusFence_of_vanishing_rows needs)?

For each accessible cell (n, p) with p ≡ 1 mod n:
  - pick each root t of x^n − 1 mod p (each degree-one prime 𝔭_t above p),
  - census C(t) = { w ∈ {−1,0,1}^n : exactly-6 support, Σ_j w_j t^j ≡ 0 mod p },
  - measure |C(t)|, rank of C(t) over ℚ (via rank mod a large auxiliary prime q ∤ everything,
    plus rank mod p for contrast), and the common coverage of a maximal-rank subfamily
    (# roots t' where ALL rows of the subfamily vanish).

Fence theorem (kernel-checked, _G87CoverageDivisibility.lean): a full-rank d×d support-six
family vanishing at s distinct roots forces s·log p ≤ (d/2)·log 6. The forcing direction of
the G82 race needs a full-rank family with LARGE common coverage. The G82 addendum probe
measured per-relation coverage ≡ 1; here we measure whether full rank is even attainable.

VERDICT semantics:
  - rank == n     : fence hypothesis attainable; forcing direction alive at this cell.
  - rank == n − 1 : census spans exactly the hyperplane "eval at t = 0" ∩ lattice — the
                    natural maximum (every census row satisfies ONE linear relation over ℚ
                    only if eval_t is rational... it is NOT — eval at t is mod-p only, so
                    over ℚ full rank n is a priori possible).
  - rank << n     : census is degenerate; the forcing route is vacuous at this cell.
"""
import itertools, sys
import numpy as np

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def nth_roots(n, p):
    """all t in [1,p) with t^n ≡ 1 mod p (p ≡ 1 mod n => exactly n of them)"""
    # find generator of the group of n-th roots: g = h^((p-1)/n) for h primitive-ish
    for h in range(2, p):
        g = pow(h, (p-1)//n, p)
        if g != 1:
            # check order exactly n (n = 2^k here so check g^(n/2) != 1)
            if pow(g, n//2, p) != 1:
                break
    roots = []
    x = 1
    for _ in range(n):
        roots.append(x)
        x = x*g % p
    assert len(set(roots)) == n
    return roots

def census_rows(n, p, t):
    """support-6 ±1 vectors w with Σ w_j t^j ≡ 0 mod p (vectorized over sign patterns)"""
    tp = np.array([pow(t, j, p) for j in range(n)], dtype=np.int64)
    rows = []
    signs = np.array(list(itertools.product((1,-1), repeat=6)), dtype=np.int64)  # 64 x 6
    for supp in itertools.combinations(range(n), 6):
        vals = tp[list(supp)]                      # 6
        tot = (signs @ vals) % p                   # 64
        for k in np.nonzero(tot == 0)[0]:
            w = np.zeros(n, dtype=np.int64)
            w[list(supp)] = signs[k]
            rows.append(w)
    return np.array(rows, dtype=np.int64) if rows else np.zeros((0, n), dtype=np.int64)

def rank_mod(M, q):
    """rank of integer matrix M mod prime q (Gaussian elimination)"""
    A = (M % q).astype(np.int64).copy()
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c] % q:
                piv = i; break
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), q-2, q)
        A[r] = A[r] * inv % q
        mask = A[:, c] % q != 0
        mask[r] = False
        A[mask] = (A[mask] - np.outer(A[mask, c], A[r])) % q
        r += 1
        if r == m: break
    return r

def common_coverage(rows, roots, p, n):
    """# roots t' where ALL rows vanish mod p"""
    cov = 0
    for t in roots:
        tp = np.array([pow(t, j, p) for j in range(n)], dtype=np.int64)
        if np.all((rows @ tp) % p == 0):
            cov += 1
    return cov

Q_AUX = 1_000_003  # auxiliary prime for characteristic-0 rank proxy (entries in {-1,0,1};
                   # rank mod q >= true rank is false, rank mod q <= rank_Q; equality holds
                   # unless q divides a maximal minor — vanishing there is measure-zero-ish;
                   # we ALSO report rank mod a second prime to cross-check)
Q_AUX2 = 999_983

def main():
    cells = [(16, 97), (16, 193), (16, 257), (32, 641), (32, 769), (32, 1153)]
    print("# G87V census-rank probe — is the fence hypothesis (full rank) attainable?")
    for n, p in cells:
        if not isprime(p) or (p-1) % n:
            print(f"  SKIP ({n},{p})"); continue
        roots = nth_roots(n, p)
        ranks, sizes, covs = [], [], []
        for t in roots:
            if t == 1:  # trivial embedding: Σ w_j = 0 — different structure, keep separate
                continue
            M = census_rows(n, p, t)
            if M.shape[0] == 0:
                sizes.append(0); ranks.append(0); covs.append(0); continue
            r1 = rank_mod(M, Q_AUX); r2 = rank_mod(M, Q_AUX2)
            rp = rank_mod(M, p)
            sizes.append(M.shape[0]); ranks.append((r1, r2, rp))
            covs.append(common_coverage(M, roots, p, n))
        uniq_r = sorted(set(ranks))
        print(f"cell (n={n}, p={p}): #census per nontrivial root: "
              f"min={min(sizes)} max={max(sizes)}; ranks (q1,q2,mod p): {uniq_r}; "
              f"full-census common coverage per root: {sorted(set(covs))}")
        d_needed = n  # square d x d family in the Lean fence with d = n columns
        attain = [r for r in ranks if isinstance(r, tuple) and r[0] >= d_needed]
        print(f"   -> full rank n={n} attainable at {len(attain)}/{len(ranks)} roots "
              f"(fence threshold s* = (n/2)*log6/(2*log p) = "
              f"{(n/2)*np.log(6)/(2*np.log(p)):.2f})")
    print("READ: rank == n at some root => forcing direction has a live hypothesis (then the")
    print("fence caps its coverage); rank << n everywhere => piece-(3) forcing VACUOUS at")
    print("accessible cells; rank == n-1 with rank mod p == n-1 => census sits exactly on")
    print("the eval-at-t hyperplane mod p but spans it — the sharp intermediate case.")

if __name__ == "__main__":
    main()
