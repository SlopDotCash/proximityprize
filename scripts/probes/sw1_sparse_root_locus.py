#!/usr/bin/env python3
"""
SW1 / lane SPARSE — exact root-locus average of the CORE energy and the distribution of the
primitive-root count Z(P) over spurious signed 2r-nomials.

Setting.  g generates mu_n <= F_p^x (n = 2^mu, p = 1 mod n).  A signed tuple
(a_1..a_r | b_1..b_r) in (Z/n)^{2r} defines P(T) = sum T^{a_i} - sum T^{b_i} in Z[T]/(T^n-1).
  E_r^{(u)} := #{tuples : P(g^u) = 0}            (energy at embedding g^u)
  Z(P)      := #{u in (Z/n)^x : P(g^u) = 0}      (primitive-root count of P)
Galois dilation a -> c*a (c a unit) is a bijection on tuples with P_{c.t}(g^u) = P_t(g^{uc}), so
  (I1)  E_r^{(u)} = E_r^{(1)} =: E_r for every unit u,
  (I2)  sum_{tuples} Z(P) = sum_u E_r^{(u)} = phi(n) * E_r        (phi(n) = n/2).
Tuples with Phi_n | P in Z[T] ("char-0 / Lam-Leung relations") have Z(P) = n/2 (all primitive
roots); all others are SPURIOUS.  For p > 2r the converse holds (Z(P) = n/2  iff  Phi_n | P),
since P mod (T^{n/2}+1) has integer coefficients of absolute value <= 2r.

What this probe measures (all exact integer arithmetic):
  (A) the identity (I1)/(I2) on every cell (hard FAIL on violation);
  (B) the converse  Z(P) = n/2  <=>  Phi_n | P  on every enumerated tuple (hard FAIL);
  (C) the full distribution of Z(P) over spurious tuples: histogram, max, and the fraction of
      the spurious mass  S := sum_{spurious} Z(P) = (n/2)(E_r - E_r^0)  carried by Z = 1;
  (D) a structural decomposition of the Z >= 2 spurious tuples:
        'refl'  : the signed multiset is invariant under a -> s - a for some s (self-reciprocal
                  P), which forces the vanishing set to be closed under u -> -u, hence Z even;
        'tower' : P = Phi_n * A + Q(T^2) for some tuple Q at level n/2 (equivalently the odd-
                  exponent part of P is Phi_n-divisible) — then Z_n(P) = 2 * Z_{n/2}(Q);
        'other' : neither (accidental multiple vanishing).
  (E) the trivial two-sided window  E_r - E_r^0 <= #{spurious : Z >= 1} <= (n/2)(E_r - E_r^0),
      which is the exact content of "per-P root bounds are index-blind" (see KB note).

Enumeration: tuples are enumerated as pairs of r-multisets of Z/n with multiplicity weights
(r!/prod m_i!)^2; a tuple with Z = z is in exactly z of the n/2 fibers V_u, and by (I1) each
fiber has the same Z-profile, so  #{tuples : Z = z} = (n/2)/z * #{tuples in V_1 : Z = z}.
Only V_1 (the fiber at the base embedding) is enumerated.

Usage:  python3 sw1_sparse_root_locus.py [--quick]
Exit code 0 = PASS (identities and converse verified on every cell), 1 = FAIL.
"""
import sys
import itertools
from math import factorial
from collections import Counter, defaultdict


def first_generator(p, n):
    """Return a generator of the order-n subgroup of F_p^x."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    for c in range(2, p):
        h = pow(c, m, p)
        # check exact order n: h^(n/2) != 1 (n is a power of two, n >= 2)
        if pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError("no generator")


def is_prime(q):
    if q < 2:
        return False
    if q % 2 == 0:
        return q == 2
    i = 3
    while i * i <= q:
        if q % i == 0:
            return False
        i += 2
    return True


def primes_1_mod_n(n, count, start=None):
    """First `count` primes p = 1 mod n with p > start (default start = n^2)."""
    out = []
    q = (start if start is not None else n * n) // n * n + 1
    while len(out) < count:
        if is_prime(q):
            out.append(q)
        q += n
    return out


def multisets(n, r):
    """All r-multisets of Z/n as sorted tuples, with ordering weight r!/prod(m_i!)."""
    out = []
    for ms in itertools.combinations_with_replacement(range(n), r):
        cnt = Counter(ms)
        w = factorial(r)
        for v in cnt.values():
            w //= factorial(v)
        out.append((ms, w))
    return out


def char0_vector(a_ms, b_ms, n):
    """Coefficient vector of P mod (T^{n/2}+1) over Z (n a power of two): index b in Z/(n/2)."""
    h = n // 2
    v = [0] * h
    for a in a_ms:
        v[a % h] += (-1) ** (a // h)
    for b in b_ms:
        v[b % h] -= (-1) ** (b // h)
    return v


def is_char0(a_ms, b_ms, n):
    return all(c == 0 for c in char0_vector(a_ms, b_ms, n))


def is_reflective(a_ms, b_ms, n):
    """Signed multiset invariant under a -> s - a (mod n) for some shift s."""
    ca, cb = Counter(a_ms), Counter(b_ms)
    for s in range(n):
        if all(ca[(s - a) % n] == ca[a] for a in ca) and \
           all(cb[(s - b) % n] == cb[b] for b in cb):
            return True
    return False


def is_tower(a_ms, b_ms, n):
    """One parity part of P is Phi_n-divisible, i.e. P = Phi_n*A + T^e * Q(T^2) in
    Z[T]/(T^n-1) with e in {0,1}; then P(x) = P(-x) at every primitive root and
    Z_n(P) = 2 * Z_{n/2}(Q) (tower descent to the level-n/2 tuple Q)."""
    h = n // 2
    for par in (0, 1):
        v = [0] * h
        for a in a_ms:
            if a % 2 == par:
                v[a % h] += (-1) ** (a // h)
        for b in b_ms:
            if b % 2 == par:
                v[b % h] -= (-1) ** (b // h)
        if all(c == 0 for c in v):
            return True
    return False


def run_cell(n, p, r, verbose=True):
    g = first_generator(p, n)
    units = [u for u in range(n) if u % 2 == 1]
    phi = len(units)
    # powers table: pw[a][u] = g^{u a}
    gu = [pow(g, u, p) for u in range(n)]
    pw = [[pow(gu[u], a, p) for u in range(n)] for a in range(n)]
    ms = multisets(n, r)
    # base-embedding sums and full unit-profile of each multiset
    base = {}
    prof = {}
    for X, w in ms:
        base[X] = sum(pw[a][1] for a in X) % p
        prof[X] = tuple(sum(pw[a][u] for a in X) % p for u in units)
    # fiber V_1: pairs (X, Y) with equal base sums
    by_sum = defaultdict(list)
    for X, w in ms:
        by_sum[base[X]].append((X, w))
    E1 = 0                      # E_r^{(1)} with multiplicities
    E_by_u = [0] * phi          # E_r^{(u)} recomputed directly (identity check I1)
    # direct per-u energies via profiles
    for k, u in enumerate(units):
        d = defaultdict(int)
        for X, w in ms:
            d[prof[X][k]] += w
        E_by_u[k] = sum(v * v for v in d.values())
    hist_fiber = Counter()      # Z -> weighted count of V_1-tuples with that Z (spurious only)
    mech = defaultdict(Counter)  # Z -> Counter of mechanism labels (weighted)
    E0 = 0                      # char-0 relation count (tuples with Phi_n | P)
    Zmax_sp = 0
    bad_converse = 0
    examples = {}
    for s, lst in by_sum.items():
        for X, wx in lst:
            px = prof[X]
            for Y, wy in lst:
                w = wx * wy
                E1 += w
                Z = sum(1 for k in range(phi) if px[k] == prof[Y][k])
                c0 = is_char0(X, Y, n)
                if (Z == phi) != c0:
                    bad_converse += w
                if c0:
                    E0 += w
                    continue
                hist_fiber[Z] += w
                if Z > Zmax_sp:
                    Zmax_sp = Z
                if Z >= 2:
                    if is_reflective(X, Y, n):
                        lab = 'refl'
                    elif is_tower(X, Y, n):
                        lab = 'tower'
                    else:
                        lab = 'other'
                    # observable: closure type of the vanishing set itself
                    vs = {units[k] for k in range(phi) if px[k] == prof[Y][k]}
                    neg_closed = all((-u) % n in vs for u in vs)
                    half_closed = all((u + n // 2) % n in vs for u in vs)
                    lab += '|' + ('neg' if neg_closed else '') + ('half' if half_closed else '') \
                        + ('' if (neg_closed or half_closed) else 'free')
                    mech[Z][lab] += w
                    if (Z, lab) not in examples:
                        examples[(Z, lab)] = (X, Y, sorted(vs))
    # identity checks
    ok_I1 = all(e == E1 for e in E_by_u)
    sumZ_total = sum(z * (phi // z if phi % z == 0 else phi / z) * c
                     for z, c in hist_fiber.items()) + phi * E0
    # #{tuples : Z=z} = (phi/z) * #{V_1 tuples : Z = z}; sum_z z*#{Z=z} = phi * sum_z #{V_1: Z=z}
    sumZ_total = phi * (sum(hist_fiber.values()) + E0)
    ok_I2 = (sumZ_total == sum(E_by_u))
    spurious_mass = phi * (E1 - E0)                  # sum_{spurious} Z(P)
    # number of spurious tuples with Z >= 1 (union of the fibers)
    n_union = sum((phi * c) // z for z, c in hist_fiber.items())
    # exactness: phi*c must be divisible by z (each such tuple counted z times over the fibers)
    ok_div = all((phi * c) % z == 0 for z, c in hist_fiber.items())
    mass_Z1 = phi * hist_fiber.get(1, 0)
    frac_Z1 = mass_Z1 / spurious_mass if spurious_mass else float('nan')
    wick = 1
    for k in range(1, 2 * r, 2):
        wick *= k
    if verbose:
        print(f"cell n={n} p={p} r={r} g={g} phi={phi}")
        print(f"  E_r = {E1}   E_r^0(char0) = {E0}   n^{2*r}/p = {n**(2*r)/p:.3f}"
              f"   Wick (2r-1)!! n^r = {wick * n**r}")
        print(f"  identity I1 (all E^(u) equal): {ok_I1}   I2 (sum Z = phi*E_r): {ok_I2}"
              f"   converse Z=n/2<=>char0 violations: {bad_converse}   divisibility ok: {ok_div}")
        print(f"  spurious mass sum Z = {spurious_mass}; #spurious with Z>=1 = {n_union};"
              f"  window [E-E0, phi(E-E0)] = [{E1 - E0}, {spurious_mass}];"
              f"  n_union/(E-E0) = {n_union / (E1 - E0) if E1 > E0 else float('nan'):.4f}")
        print(f"  Z-histogram over spurious tuples (Z: #tuples): "
              + ", ".join(f"{z}: {(phi * c) // z}" for z, c in sorted(hist_fiber.items())))
        print(f"  Zmax(spurious) = {Zmax_sp};  fraction of spurious mass at Z=1: {frac_Z1:.6f}")
        for z in sorted(mech):
            tot = sum(mech[z].values())
            print(f"    Z={z}: mechanisms (V_1-weighted): "
                  + ", ".join(f"{lab}={cnt}" for lab, cnt in mech[z].most_common()))
        for (z, lab), (X, Y, vs) in sorted(examples.items()):
            print(f"    example Z={z} {lab}: +{list(X)} -{list(Y)}  vanishing u-set {vs}")
    return dict(n=n, p=p, r=r, E=E1, E0=E0, ok=ok_I1 and ok_I2 and bad_converse == 0 and ok_div,
                Zmax=Zmax_sp, hist={z: (phi * c) // z for z, c in hist_fiber.items()},
                mech={z: dict(c) for z, c in mech.items()}, frac_Z1=frac_Z1,
                union=n_union, mass=spurious_mass)


def main():
    quick = '--quick' in sys.argv
    cells = []
    # (n, r, number of primes)
    plan = [(8, 2, 4), (8, 3, 4), (8, 4, 3),
            (16, 2, 4), (16, 3, 4), (16, 4, 2),
            (32, 2, 3), (32, 3, 3), (32, 4, 2),
            (64, 2, 2), (64, 3, 2)]
    if quick:
        plan = [(8, 2, 2), (8, 3, 2), (16, 2, 2), (16, 3, 1)]
    all_ok = True
    summary = []
    for n, r, np_ in plan:
        ps = primes_1_mod_n(n, np_)
        # also one "thicker" prime near n^3 for the larger cells to show the p-trend
        if n >= 16 and not quick:
            ps = ps + primes_1_mod_n(n, 1, start=n ** 3)
        for p in ps:
            res = run_cell(n, p, r)
            all_ok &= res['ok']
            summary.append(res)
            print()
    print("=" * 78)
    print("SUMMARY (n, p, r): E_r, E_r^0, Zmax_spurious, frac of spurious mass at Z=1, "
          "union/(E-E0), Z>=2 mechanisms")
    for s in summary:
        mech = "; ".join(f"Z={z}:" + "/".join(f"{k}={v}" for k, v in c.items())
                         for z, c in sorted(s['mech'].items()))
        ratio = s['union'] / (s['E'] - s['E0']) if s['E'] > s['E0'] else float('nan')
        print(f"  ({s['n']:3d},{s['p']:7d},{s['r']}): E={s['E']:>9d} E0={s['E0']:>8d} "
              f"Zmax={s['Zmax']:2d} fracZ1={s['frac_Z1']:.5f} union/(E-E0)={ratio:.4f} {mech}")
    if all_ok:
        print("PASS: identities I1/I2, the converse Z=n/2<=>Phi_n|P (p>2r), and fiber "
              "divisibility hold on every cell")
        sys.exit(0)
    print("FAIL: an identity or the converse was violated on some cell")
    sys.exit(1)


if __name__ == '__main__':
    main()
