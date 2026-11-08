#!/usr/bin/env python3
r"""
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
  * A bad scalar is FRESH if none of its nonjoint witness sets contains a degenerate core -- its
    constraint block is 'fresh rank' not explained by any pencil.

MCA BADNESS IS EXISTENTIAL (audit 2026-10-28 finding L122; crosslinks T62, L119): z is bad iff
SOME close codeword of u0+z*u1 has an agreement set on which (u0,u1) is not jointly explained.
`bad_scalars` therefore decodes the COMPLETE list of distinct close codewords (shared helpers
`close_codewords` / `mca_witnesses` in probe_syz28_verify_classification) and keeps every
nonjoint witness; one jointly explained close codeword does not discard z.  Attribution uses
any nonjoint witness containing a degenerate core (the pencil argument applies to each).
Regression fixture (F17, n16, k8, s11): u0=[0]*11+[1,0,0,0,0], u1=[0]*11+[4,12,9,1,4]; at
z=1 the zero codeword is close on {0..10} (jointly explained), while prod_(a=0..6)(X-a) is
close on {0..6,11..15} (size 12, not jointly explained), so z=1 is MCA-bad.

CLAIMS TESTED (n in {16,32}, k=n/2, band cores, GF(p)):
  (A) PENCIL STACKS (built as u0+z_i*u1 poly on core C_i): every bad z is pencil-attributed
      (#fresh == 0), and #bad <= sum(n-s_i) = the pencil pool.  [attribution complete]
  (B) ADVERSARIAL RANDOM STACKS: measure #bad, #fresh, and #bad vs the SYZ22 budget n-1.
      The honest law: whenever attribution is complete (#fresh==0) #bad <= sum_i(n-s_i);
      the residual is exactly the attribution step (bounding #fresh).
"""
import random
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, A_C_basis, dual_basis_cached)
from probe_syz28_verify_classification import (build_interp_mats, close_codewords,
    pair_joint_on, mca_witnesses)

# ---- complete list decoding via precomputed interpolation matrices (pigeonhole window) ----
_MATCACHE = {}
def _interp_mats(n, k, s, p):
    """Cached `build_interp_mats` (which raises if its window is not complete for (n,k,s))."""
    key = (n, k, s, p)
    if key not in _MATCACHE: _MATCACHE[key] = build_interp_mats(n, k, s, p)
    return _MATCACHE[key]

def decode_close_codewords(w, n, k, s, p):
    """All distinct close codewords of w with their full agreement sets (complete decoder)."""
    return close_codewords(w, _interp_mats(n, k, s, p), n, k, s, p)

def pairjoint_on(D, u0, u1, n, k, s, p):
    """pairJointAgreesOn D (requires |D| >= k; MCA witness sets here have |D| >= s >= k)."""
    return pair_joint_on(D, u0, u1, k, p)

def bad_scalars(u0, u1, n, k, s, p):
    """Return list of (z, witnesses) for mca-bad scalars, where witnesses is the NONEMPTY list of
    all nonjoint witness sets of z (one per distinct close codeword of u0+z*u1 whose agreement
    set is not pairJointAgreesOn).  Every close codeword is tested (existential condition)."""
    mats = _interp_mats(n, k, s, p)
    out = []
    for z in range(p):
        ws = mca_witnesses(u0, u1, z, mats, n, k, s, p)
        if ws: out.append((z, ws))
    return out

def has_degenerate_core(S, cores, u0, u1, n, k, s, p):
    """S 'contains a degenerate core' if some core C (|C|>=s) has C<=S and pairJointAgreesOn C."""
    for C in cores:
        Cs = set(C)
        if Cs <= S and pairjoint_on(list(Cs), u0, u1, n, k, s, p):
            return True
    return False

def is_attributed(witnesses, cores, u0, u1, n, k, s, p):
    """Pencil-attributed iff SOME nonjoint witness of the scalar contains a degenerate core."""
    return any(has_degenerate_core(S, cores, u0, u1, n, k, s, p) for S in witnesses)

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
        fresh = sum(0 if is_attributed(ws, cores, u0, u1, n, k, s, p) else 1 for _, ws in bs)
        max_bad = max(max_bad, len(bs)); max_fresh = max(max_fresh, fresh)
        if len(bs) > pool: viol += 1
    # (B) adversarial random stacks
    adv_max_bad = 0; adv_max_fresh = 0; adv_bad_over_budget = 0
    for _ in range(stacks):
        u0 = [rng.randrange(p) for _ in range(n)]
        u1 = [rng.randrange(p) for _ in range(n)]
        bs = bad_scalars(u0, u1, n, k, s, p)
        fresh = sum(0 if is_attributed(ws, cores, u0, u1, n, k, s, p) else 1 for _, ws in bs)
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
