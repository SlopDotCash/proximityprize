#!/usr/bin/env python3
"""
SYZ29 part (i): the HONEST global accounting for the pencil-yield law.

The naive statement "#mca-bad <= sum_i (n - s_i)" is NOT literally a law of an arbitrary stack:
a bad scalar's witness set S need not sit inside any core, so it need not come from a core
pencil.  The honest decomposition (what this probe measures):

    #bad  =  #pencil-attributed  +  #fresh

  * A bad scalar z is PENCIL-ATTRIBUTED to core C if its mca-witness set S_z contains a
    degenerate core: a subset D <= S_z, |D| >= s, on which the pair (u0,u1) JOINTLY agrees with
    a codeword pair (pairJointAgreesOn D).  Then on S_z \ D the line u0+z*u1 equals a codeword
    but the pair does not jointly agree, so z = -(u0-v0)(x)/(u1-v1)(x) for some x in S_z\D:
    z lies in the pencil image of D, of size <= n - |D| <= n - s.  (SYZ18/SYZ2/SYZ3 substrate.)
  * A bad scalar is FRESH if its witness set contains no degenerate core -- its constraint block
    is 'fresh rank' not explained by any pencil.

CLAIMS TESTED (n in {16,32}, k=n/2, band cores, GF(p)):
  (A) PENCIL STACKS (built as u0+z_i*u1 poly on core C_i): every bad z is pencil-attributed
      (#fresh == 0), and #bad <= sum(n-s_i) = the pencil pool.  [attribution complete]
  (B) ADVERSARIAL RANDOM STACKS: measure #bad, #fresh, and #bad vs the SYZ22 budget n-1.
      The honest law: whenever attribution is complete (#fresh==0) #bad <= sum_i(n-s_i);
      the residual is exactly the attribution step (bounding #fresh).
"""
import itertools, random
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, A_C_basis, dual_basis_cached)

# ---- fast list-decoding via precomputed interpolation matrices (pigeonhole window) ----
_MATCACHE = {}
def _interp_mats(n, k, s, p):
    key = (n, k, s, p)
    if key in _MATCACHE: return _MATCACHE[key]
    base = list(range(min(n, n - (n - s) + 2)))  # pigeonhole window; agreement>=s meets it in >=k pts
    mats = []
    for T in itertools.combinations(base, k):
        M = []
        for j in range(n):
            row = []
            for t in T:
                num = 1; den = 1
                for t2 in T:
                    if t2 == t: continue
                    num = (num * (j - t2)) % p; den = (den * (t - t2)) % p
                row.append((num * pow(den, p - 2, p)) % p)
            M.append(row)
        mats.append((T, M))
    _MATCACHE[key] = mats
    return mats

def decode_agreement_set(w, n, k, s, p):
    """Return an agreement set (>= s) of a codeword with w, or None (fast, windowed)."""
    for T, M in _interp_mats(n, k, s, p):
        vals = [w[t] for t in T]
        agree = []
        for j in range(n):
            v = 0
            for a, b in zip(M[j], vals): v += a * b
            if v % p == w[j] % p: agree.append(j)
        if len(agree) >= s: return set(agree)
    return None

def pairjoint_on(D, u0, u1, n, k, s, p):
    """pairJointAgreesOn: exist codewords v0,v1 agreeing with u0,u1 on all of D.  For |D|>=k the
    interpolant on any k-subset of D is unique; check it agrees with u0 (resp u1) on all of D."""
    D = sorted(D)
    if len(D) < k: return False
    T = D[:k]
    def interp_agrees(u):
        vals = [u[t] for t in T]
        for j in D:
            v = 0
            for ti, t in enumerate(T):
                num = 1; den = 1
                for t2 in T:
                    if t2 == t: continue
                    num = (num * (j - t2)) % p; den = (den * (t - t2)) % p
                v = (v + vals[ti] * num * pow(den, p - 2, p)) % p
            if v % p != u[j] % p: return False
        return True
    return interp_agrees(u0) and interp_agrees(u1)

def bad_scalars(u0, u1, n, k, s, p):
    """Return list of (z, witness_set) for mca-bad scalars: line delta-close AND
    NOT pairJointAgreesOn its witness set."""
    out = []
    for z in range(p):
        w = [(u0[j] + z * u1[j]) % p for j in range(n)]
        S = decode_agreement_set(w, n, k, s, p)
        if S is None: continue
        if pairjoint_on(S, u0, u1, n, k, s, p): continue  # mca filter: pair jointly agrees => not bad
        out.append((z, S))
    return out

def has_degenerate_core(S, cores, u0, u1, n, k, s, p):
    """S 'contains a degenerate core' if some core C (|C|>=s) has C<=S and pairJointAgreesOn C."""
    for C in cores:
        Cs = set(C)
        if Cs <= S and pairjoint_on(list(Cs), u0, u1, n, k, s, p):
            return True
    return False

def build_pencil_stack(cores, n, k, p, rng):
    Db = dual_basis_cached(list(range(n)), k, p)
    AC = [A_C_basis(Db, C, n, p) for C in cores]
    zs = rng.sample(range(1, p), len(cores))
    rows = []
    for i in range(len(cores)):
        for v in AC[i]:
            rows.append([v[j] % p for j in range(n)] + [(zs[i] * v[j]) % p for j in range(n)])
    r, null = rref_rank_nullbasis(rows, 2 * n, p)
    if not null: return None
    u = [0] * (2 * n)
    for b in null:
        c = rng.randrange(p)
        for j in range(2 * n): u[j] = (u[j] + c * b[j]) % p
    if all(x == 0 for x in u[n:]): return None
    return u[:n], u[n:]

def run(n, cores, p=17, stacks=25, seed=5):
    k = n // 2; s = cores[0].__len__(); rng = random.Random(seed)
    pool = sum(n - len(C) for C in cores)
    # (A) pencil stacks
    max_bad = 0; max_fresh = 0; viol = 0; tested = 0
    for _ in range(stacks):
        st = build_pencil_stack(cores, n, k, p, rng)
        if st is None: continue
        u0, u1 = st; tested += 1
        bs = bad_scalars(u0, u1, n, k, s, p)
        fresh = sum(0 if has_degenerate_core(S, cores, u0, u1, n, k, s, p) else 1 for _, S in bs)
        max_bad = max(max_bad, len(bs)); max_fresh = max(max_fresh, fresh)
        if len(bs) > pool: viol += 1
    # (B) adversarial random stacks
    adv_max_bad = 0; adv_max_fresh = 0; adv_bad_over_budget = 0
    for _ in range(stacks):
        u0 = [rng.randrange(p) for _ in range(n)]
        u1 = [rng.randrange(p) for _ in range(n)]
        bs = bad_scalars(u0, u1, n, k, s, p)
        fresh = sum(0 if has_degenerate_core(S, cores, u0, u1, n, k, s, p) else 1 for _, S in bs)
        adv_max_bad = max(adv_max_bad, len(bs)); adv_max_fresh = max(adv_max_fresh, fresh)
        if len(bs) > n - 1: adv_bad_over_budget += 1
    return dict(n=n, pool=pool, tested=tested, max_bad=max_bad, max_fresh=max_fresh,
                pool_violations=viol, adv_max_bad=adv_max_bad, adv_max_fresh=adv_max_fresh,
                adv_over_budget=adv_bad_over_budget)

if __name__ == "__main__":
    print("=== SYZ29 (i): honest global accounting  #bad = #pencil-attributed + #fresh ===")
    # n=16 SYZ28 witness (three 11-cores, pool sum(n-s)=15=n-1)
    W16 = [[1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 15],
           [1, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15],
           [0, 1, 3, 4, 5, 9, 10, 11, 12, 14, 15]]
    r = run(16, W16, p=17, stacks=25)
    print(f"n=16 (SYZ28 witness, pool sum(n-s)={r['pool']}):")
    print(f"  PENCIL stacks tested={r['tested']}  max#bad={r['max_bad']}  max#fresh={r['max_fresh']}"
          f"  #bad>pool violations={r['pool_violations']}")
    print(f"  ADVERSARIAL random stacks: max#bad={r['adv_max_bad']} max#fresh={r['adv_max_fresh']}"
          f"  #bad>n-1 count={r['adv_over_budget']}")
