"""probe_466_novel_sos_collapse.py -- LANE N5 (#466): sharpen the two load-bearing
constants of the SoS-collapse theorem (kb note
docs/kb/deltastar-466-novel-N5-sos-duality-2026-07-01.md).

BACKGROUND (the dictionary).  Encode the prize object as the 0-dimensional variety
    V = { (e_p(b*x_j))_{j<n} : b in F_p },   x_j = h^j,  h of order n = |mu_n| in F_p^x,
inside the torus (S^1)^n, cut out by |z_j|^2 = 1 and the binomial relations
    z^{a+} = z^{a-}  for  a in L := ker( Z^n -> F_p,  a |-> sum_j a_j h^j ).
A degree-d SoS proof sees exactly:
  * frequency classes  = the image  Sigma_k := S(B_1(k))  (k-fold signed sumset of mu_n,
    k = d/2) -- monomials of degree k reduce mod the visible ideal to one representative
    per frequency;
  * arithmetic axioms  = the relation vectors of l1-norm <= d  (short elements of the
    degree-one cyclotomic prime ideal p_frak = ker(Z[zeta_n] -> F_p) after the antipodal
    quotient, PLUS the antipodal char-0 relations themselves).

THE TWO CONSTANTS THIS PROBE MEASURES:

  (1) k0(beta) := min { k : Sigma_k = F_p }  (cumulative signed sumset covering fold).
      The collapse theorem's certificate degree is d0 <= C*k0 (C <= 8 bookkeeping).
      Claim to check: k0 depends on beta = log_n p only (~ beta + 1), NOT on n --
      i.e. the collapse degree is O(1) at fixed beta.

  (2) d_gen(n,p) := min { d : the lattice spanned by ALL relation vectors of l1-norm <= d
      equals L (index p in Z^n) }.  This is the honest-axiom-set threshold: with the
      poly-size axiom set {circle, antipodal, relations of norm <= D0}, the relaxed
      variety V_D0 collapses to the true V exactly when D0 >= d_gen.  Below d_gen the
      relaxation has spurious points and NO degree can certify the prize.
      Also reported: d_onset (first non-char-0 relation), rank growth, index ladder
      (index of the span in Z^n; must be a multiple of p once full rank -- sanity).

Method for (2): meet-in-the-middle enumeration of the full integer l1-ball
(split coordinates in half, hash partial sums mod p), then integer row-HNF for the
lattice index.  Everything exact (Python ints).

Scales (kept light -- the box is busy): n = 8 with 3 primes near n^4, n = 16 with
3 primes near n^4 (incl. 65537 to cross-check the Fermat anomaly), d <= 8.

Output: scripts/probes/_out_466_novel_sos_collapse.txt
"""

import sys
from itertools import combinations
from math import gcd

# ----------------------------------------------------------------------
# small number theory helpers (exact)
# ----------------------------------------------------------------------

def is_prime(m):
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def primitive_root(p):
    fac = []
    m = p - 1
    dd = 2
    while dd * dd <= m:
        if m % dd == 0:
            fac.append(dd)
            while m % dd == 0:
                m //= dd
        dd += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError


def subgroup(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    xs = [pow(h, j, p) for j in range(n)]
    assert len(set(xs)) == n
    return xs


def primes_1modn_near(n, target, count):
    """count primes p = 1 mod n with p >= target (beta ~ 4 diagonal)."""
    out = []
    p = target + ((-target) % n) + 1
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


# ----------------------------------------------------------------------
# (1) cumulative signed sumset covering fold k0
# ----------------------------------------------------------------------

def covering_fold(xs, p, kmax=12):
    """sizes of C_k, C_0={0}, C_{k+1} = C_k u (C_k + mu_n); k0 = first k with |C_k|=p.
    (signed sums are included automatically since -1 in mu_n for even n)."""
    cur = {0}
    sizes = []
    for k in range(1, kmax + 1):
        cur = cur | {(c + x) % p for c in cur for x in xs}
        sizes.append(len(cur))
        if len(cur) == p:
            return k, sizes
    return None, sizes


# ----------------------------------------------------------------------
# (2) short-relation lattice: enumeration + integer HNF index
# ----------------------------------------------------------------------

def half_vectors(dim, dmax):
    """all integer vectors v in Z^dim with l1-norm <= dmax, as (vec tuple, norm)."""
    out = [(tuple([0] * dim), 0)]
    for m in range(1, dmax + 1):
        for s in range(1, min(m, dim) + 1):
            for supp in combinations(range(dim), s):
                for comp in compositions(m, s):
                    for signs in range(1 << s):
                        v = [0] * dim
                        for i, (pos, c) in enumerate(zip(supp, comp)):
                            v[pos] = c if (signs >> i) & 1 == 0 else -c
                        out.append((tuple(v), m))
    return out


def compositions(m, s):
    """compositions of m into s positive parts."""
    if s == 1:
        yield (m,)
        return
    for first in range(1, m - s + 2):
        for rest in compositions(m - first, s - 1):
            yield (first,) + rest


def relations_upto(xs, p, dmax):
    """all a in Z^n, l1-norm <= dmax, sum_j a_j x_j = 0 mod p, grouped by norm.
    Meet-in-the-middle on the two coordinate halves."""
    n = len(xs)
    nh = n // 2
    xs1, xs2 = xs[:nh], xs[nh:]
    H1 = half_vectors(nh, dmax)
    H2 = half_vectors(n - nh, dmax)
    d1 = {}
    for v, m in H1:
        val = sum(c * x for c, x in zip(v, xs1)) % p
        d1.setdefault(val, []).append((v, m))
    rels = {m: [] for m in range(1, dmax + 1)}
    for v2, m2 in H2:
        val2 = sum(c * x for c, x in zip(v2, xs2)) % p
        for v1, m1 in d1.get((-val2) % p, ()):
            m = m1 + m2
            if 0 < m <= dmax:
                rels[m].append(v1 + v2)
    return rels


def extgcd(a, b):
    """(g, u, v) with u*a + v*b = g = gcd(a,b), g >= 0."""
    old_r, r = a, b
    old_u, u = 1, 0
    old_v, v = 0, 1
    while r:
        qq = old_r // r
        old_r, r = r, old_r - qq * r
        old_u, u = u, old_u - qq * u
        old_v, v = v, old_v - qq * v
    if old_r < 0:
        old_r, old_u, old_v = -old_r, -old_u, -old_v
    return old_r, old_u, old_v


def hnf_add(basis, row):
    """add integer row to an echelon basis (dict pivot_col -> row with that
    leftmost-nonzero pivot).  Textbook extended-gcd update; span is preserved."""
    row = list(row)
    while True:
        piv = next((i for i, c in enumerate(row) if c != 0), None)
        if piv is None:
            return
        if piv not in basis:
            if row[piv] < 0:
                row = [-c for c in row]
            basis[piv] = row
            return
        b = basis[piv]
        g, u, v = extgcd(row[piv], b[piv])
        newb = [u * ri + v * bi for ri, bi in zip(row, b)]      # pivot value g > 0
        row = [(b[piv] // g) * ri - (row[piv] // g) * bi
               for ri, bi in zip(row, b)]                        # pivot -> 0
        basis[piv] = newb


def basis_index(basis, n):
    """index [Z^n : span] from an echelon basis; (None, rank) if rank < n."""
    if len(basis) < n:
        return None, len(basis)
    det = 1
    for piv in sorted(basis):
        det *= basis[piv][piv]
    return abs(det), n


def is_charzero(vec, n):
    """does the relation come from the antipodal (Lam-Leung 2-power) sublattice L0?
    L0 = span{ e_j + e_{j+n/2} }: a in L0  iff  a_j = a_{j+n/2} is NOT it --
    L0 membership: a = sum c_j (e_j + e_{j+n/2})  iff  a_j - a_{j+n/2} determines...
    correct test: a in L0 iff the 'odd part' vanishes: a_j' := a_j - a_{j+n/2}
    -- no: e_j + e_{j+n/2} has a_j = a_{j+n/2} = c_j.  So a in L0 iff
    a_j == a_{j+n/2} for all j < n/2?  No: L0 = { a : a_j = a_{j+n/2} } has rank n/2. Yes.
    (Because the generators are exactly e_j + e_{j+n/2}.)"""
    nh = n // 2
    return all(vec[j] == vec[j + nh] for j in range(nh))


def analyze(n, p, dmax, out):
    xs = subgroup(n, p)
    # sanity: antipodal structure x_{j+n/2} = -x_j
    nh = n // 2
    assert all((xs[j] + xs[j + nh]) % p == 0 for j in range(nh)), "antipodal sanity"
    k0, sizes = covering_fold(xs, p)
    out.append(f"\n===== n={n}, p={p}  (beta = log_n p = {plog(n, p):.3f}) =====")
    out.append(f"covering fold: |C_k| = {sizes}  ->  k0 = {k0}")
    rels = relations_upto(xs, p, dmax)
    basis = {}
    d_onset = None
    d_gen = None
    for d in range(1, dmax + 1):
        new = rels[d]
        n_wrap = sum(1 for v in new if not is_charzero(v, n))
        if n_wrap and d_onset is None:
            d_onset = d
        for v in new:
            hnf_add(basis, v)
        idx, rank = basis_index(basis, n)
        tag = ""
        if idx is not None:
            mult = idx // p if idx % p == 0 else None
            tag = f" index = {idx} = p*{mult}" if mult is not None else f" index = {idx} (NOT mult of p -- BUG?)"
            if idx == p and d_gen is None:
                d_gen = d
                tag += "   <-- d_gen"
        out.append(f"  d={d}: #new rel = {len(new):6d} (wraparound {n_wrap:5d}), "
                   f"rank = {rank:2d}{tag}")
    out.append(f"  SUMMARY n={n} p={p}: k0 = {k0}, d_onset(wraparound) = {d_onset}, "
               f"d_gen = {d_gen if d_gen else f'>{dmax}'}")
    return k0, d_onset, d_gen


def plog(n, p):
    from math import log
    return log(p) / log(n)


def main():
    out = []
    out.append("PROBE 466 N5 SOS-COLLAPSE CONSTANTS (lane N5-sos-duality)")
    out.append("k0 = covering fold of mu_n in F_p (collapse certificate degree d0 <= ~8*k0)")
    out.append("d_gen = l1-generation radius of the relation lattice L (honest-axiom threshold)")
    results = []
    for n, dmax in ((8, 8), (16, 8)):
        target = n ** 4
        ps = primes_1modn_near(n, target, 3)
        if n == 16 and 65537 not in ps:
            ps = [65537] + ps[:2]
        for p in ps:
            results.append((n, p) + analyze(n, p, dmax, out))
    out.append("\n================ CROSS-SCALE TABLE ================")
    out.append(f"{'n':>4} {'p':>8} {'beta':>6} {'k0':>4} {'d_onset':>8} {'d_gen':>6}")
    for n, p, k0, d_on, d_gen in results:
        out.append(f"{n:>4} {p:>8} {plog(n, p):>6.3f} {str(k0):>4} {str(d_on):>8} "
                   f"{str(d_gen) if d_gen else '>8':>6}")
    out.append("""
READING: if k0 is flat in n at fixed beta (expected ~beta+1) the collapse degree is
O(1) at the prize point; d_gen flat-and-small means the collapse persists for the
HONEST poly-size axiom set (circle + antipodal + norm-<=d_gen relations).""")
    text = "\n".join(out)
    print(text)
    with open("scripts/probes/_out_466_novel_sos_collapse.txt", "w") as f:
        f.write(text + "\n")


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    main()
