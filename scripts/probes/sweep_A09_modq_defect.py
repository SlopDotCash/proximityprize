#!/usr/bin/env python3
# sweep_A09_modq_defect.py  —  Actionable A09 (delta* / proximity-gap prize, #407)
#
# GOAL: directly sample the mod-q additive-energy DEFECT of the e_2=0 count.
#
# Object (q-independent char-0 core, cf. issue400-e2zero-singles-decomposition):
#   For S subset of mu_n with |S|=w, "e_2(S)=0" means the 2nd elementary symmetric
#   function of {zeta^i : i in S} vanishes, equivalently e_1^2 = p_2 (power sum).
#   The prize-relevant count is
#       N(n,w; field) = #{ distinct e_1(S) : S, |S|=w, e_2(S)=0, e_1(S) != 0 }.
#
#   In CHAR 0, zeta = primitive complex n-th root; {1,zeta,...,zeta^{n/2-1}} is a
#   Q-basis (n=2^mu), so e_1, p_2 are exact integer vectors in Z[zeta]/(zeta^{n/2}+1).
#
#   Over F_q (q = 1 mod n), zeta in F_q is a primitive n-th root. Now
#   {1,...,zeta^{n/2-1}} is NOT F_q-linearly independent: Phi_n splits, so there are
#   extra linear relations mod q. Two effects:
#     (A) SATURATION: distinct char-0 e_1 vectors can COLLIDE mod q  -> count can DROP.
#     (B) HALO CARRIERS: sets with e_2 != 0 in char 0 can have e_2 = 0 mod q
#         (a "pure mod-p vanishing coincidence") -> NEW e_1 values -> count can RISE.
#   The signed quantity  defect = N(F_q) - N(char0)  is the per-q mod-q defect = k_D.
#
# This probe:
#   (1) tabulates  N(char0), N(F_q), defect = N(F_q)-N(char0)  for n in {16,32,64},
#       a window of w, across MANY primes q = 1 mod n  ->  the per-q SPREAD.
#   (2) at n=16, w=6, hunts the flagged divergence: sets with char-0 e_2 != 0 but
#       e_2 = 0 mod q (halo carriers), and reports alpha = signed root-sum e_1 with
#       q | N(alpha) (the cyclotomic-norm collision).
#
# EVIDENCE not proof.  Run:  python scripts/probes/sweep_A09_modq_defect.py

import itertools
from sympy import isprime, primitive_root

# ---------- char-0 exact arithmetic in Z[zeta_n]/(zeta^{n/2}+1) ----------
# vector length h=n/2, index i = coeff of zeta^i, zeta^{h+j} = -zeta^j.

def vec_from_pow(e, n):
    """zeta^e as length-h vector."""
    h = n // 2
    e %= n
    v = [0] * h
    if e < h:
        v[e] += 1
    else:
        v[e - h] -= 1
    return v

def e1_vec(A, n):
    h = n // 2
    v = [0] * h
    for a in A:
        a %= n
        if a < h:
            v[a] += 1
        else:
            v[a - h] -= 1
    return tuple(v)

def p2_vec(A, n):
    h = n // 2
    v = [0] * h
    for a in A:
        b = (2 * a) % n
        if b < h:
            v[b] += 1
        else:
            v[b - h] -= 1
    return tuple(v)

def sq_vec(v, n):
    """square of a length-h vector in the ring."""
    h = n // 2
    out = [0] * h
    for i in range(h):
        if v[i] == 0:
            continue
        for j in range(h):
            if v[j] == 0:
                continue
            k = i + j
            c = v[i] * v[j]
            if k < h:
                out[k] += c
            else:
                out[k - h] -= c
    return tuple(out)

def e2_is_zero_char0(A, n):
    """e_2 = 0  <=>  e_1^2 = p_2  (since e_1^2 = p_1^2 = p_2 + 2 e_2)."""
    return sq_vec(e1_vec(A, n), n) == p2_vec(A, n)

# ---------- F_q evaluation ----------

def zeta_modq(q, n):
    g = primitive_root(q)
    return pow(g, (q - 1) // n, q)

def eval_vec_modq(v, z, q):
    """evaluate length-h vector sum_i v_i zeta^i at zeta=z mod q."""
    acc = 0
    zp = 1
    for vi in v:
        if vi:
            acc = (acc + vi * zp) % q
        zp = (zp * z) % q
    return acc % q

def e1_val_modq(A, z, q, n):
    return eval_vec_modq(list(e1_vec(A, n)), z, q)

def e2_is_zero_modq(A, z, q, n):
    """e_2 = 0 mod q  <=>  e_1^2 - p_2 = 0 mod q evaluated at the actual root z."""
    e1 = e1_val_modq(A, z, q, n)
    p2 = eval_vec_modq(list(p2_vec(A, n)), z, q)
    return (e1 * e1 - p2) % q == 0

# ---------- counts ----------

def char0_count(n, w):
    """N(char0) = #distinct e_1 over e_2=0, e_1 != 0 (exact)."""
    s = set()
    for A in itertools.combinations(range(n), w):
        if e2_is_zero_char0(A, n):
            ev = e1_vec(A, n)
            if any(ev):
                s.add(ev)
    return len(s)

def modq_count(n, w, q):
    """N(F_q) = #distinct e_1 mod q over {e_2=0 mod q, e_1 != 0 mod q}."""
    z = zeta_modq(q, n)
    s = set()
    for A in itertools.combinations(range(n), w):
        if e2_is_zero_modq(A, z, q, n):
            e1 = e1_val_modq(A, z, q, n)
            if e1 != 0:
                s.add(e1)
    return len(s), z

# ---------- (1) defect spread table ----------

def primes_1_mod_n(n, count, start_m=1):
    out = []
    m = start_m
    while len(out) < count:
        p = n * m + 1
        if isprime(p):
            out.append(p)
        m += 1
    return out

def spread_table(n, w, nprimes=12):
    c0 = char0_count(n, w)
    print(f"\n=== n={n}  w={w}   N(char0)={c0} ===")
    print(f"{'q':>9} {'N(F_q)':>7} {'defect':>7}")
    qs = primes_1_mod_n(n, nprimes)
    defects = []
    for q in qs:
        nq, _ = modq_count(n, w, q)
        d = nq - c0
        defects.append(d)
        flag = ""
        if d > 0:
            flag = "  <== RISE (halo carriers)"
        elif d < 0:
            flag = "  <== DROP (saturation)"
        print(f"{q:>9} {nq:>7} {d:>+7}{flag}")
    if defects:
        print(f"  defect: min={min(defects):+d} max={max(defects):+d} "
              f"spread={max(defects)-min(defects)} mean={sum(defects)/len(defects):+.2f}")
    return c0, defects

# ---------- (2) n=16,w=6 halo-carrier hunt ----------

def factor_norm_collision(A, n, q):
    """Return alpha=e_1 vector and whether q | N(alpha) (the resultant / field norm).
    N(alpha)=Res(Phi_n, alpha_poly) but for the splitting prime q|N(alpha) <=>
    alpha(zeta)=0 for SOME primitive n-th root zeta mod q.  We just report e_1 mod q at z."""
    z = zeta_modq(q, n)
    return e1_val_modq(A, z, q, n)

def halo_hunt(n, w, nprimes=8):
    print(f"\n=== HALO-CARRIER HUNT  n={n} w={w} ===")
    print("sets with e_2 != 0 in char 0 but e_2 = 0 mod q  (pure mod-q vanishing)")
    # first list char-0 e_2=0 sets count for context
    c0sets = [A for A in itertools.combinations(range(n), w) if e2_is_zero_char0(A, n)]
    print(f"  char-0 e_2=0 sets: {len(c0sets)}  (distinct nonzero e_1 = {char0_count(n,w)})")
    qs = primes_1_mod_n(n, nprimes)
    for q in qs:
        z = zeta_modq(q, n)
        halo = []
        for A in itertools.combinations(range(n), w):
            if e2_is_zero_char0(A, n):
                continue  # only NEW ones
            if e2_is_zero_modq(A, z, q, n):
                halo.append(A)
        # characterize: how many distinct NEW e_1 values do they contribute?
        newe1 = set()
        for A in halo:
            v = e1_val_modq(A, z, q, n)
            if v != 0:
                newe1.add(v)
        print(f"  q={q:>7}: #halo-sets={len(halo):>4}  #new-distinct-e1(nonzero)={len(newe1):>4}")
        if halo and q == qs[0]:
            # show a couple of explicit witnesses
            for A in halo[:3]:
                e2c0 = sq_vec(e1_vec(A, n), n)  # = e1^2; e2 != p2 in char0
                print(f"      witness S={A}  e1(F_q)={e1_val_modq(A,z,q,n)}")

# ---------- main ----------

if __name__ == "__main__":
    print("A09: mod-q additive-energy defect of the e_2=0 count (#407 prize core)")
    print("defect = N(F_q) - N(char0).  RISE = halo carriers (k_D > 0), DROP = saturation.")

    # (1) per-q spread at constant-ish rate windows
    # n=16: w in {4,6,8}; n=32: w in {4,6}; n=64: w=4 (combinatorics bound the loop)
    spread_table(16, 4, nprimes=12)
    spread_table(16, 6, nprimes=12)
    spread_table(16, 8, nprimes=12)
    spread_table(32, 4, nprimes=10)
    spread_table(32, 6, nprimes=8)
    spread_table(64, 4, nprimes=8)

    # (2) the flagged n=16,w=6 char-0 / F_q divergence
    halo_hunt(16, 6, nprimes=8)
