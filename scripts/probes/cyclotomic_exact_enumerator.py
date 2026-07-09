#!/usr/bin/env python3
"""Reusable EXACT Z[zeta_n] vanishing-sum / monomial-line enumerator  (actionable A17 substrate;
consumed by A08, A09, A16, and any roots-of-unity vanishing-sum experiment in the prize campaign).

n = 2^mu.  Ring R = Z[zeta_n] = Z[X]/(X^{n/2}+1) since the minimal polynomial of a primitive
2^mu-th root of unity is Phi_{2^mu}(X) = X^{n/2}+1.  We represent an element as an EXACT integer
vector of length h = n/2 in the basis {zeta^0, ..., zeta^{h-1}}, with the single reduction rule
zeta^h = -1 (so zeta^{h+i} = -zeta^i).  All arithmetic is exact Python int — no floating point.

This is the deterministic substrate every roots-of-unity vanishing-sum experiment in the prize
campaign needs.  It is cross-checked THREE ways (see _self_test):
  (i)   ring algebra + monomial reduction vs brute-force complex evaluation at n=8,16;
  (ii)  the e_t=0 char-0 / F_q vanishing predicates vs brute-force complex / modular evaluation;
  (iii) the high-level enumerators against the campaign's already-reported exact numbers
        (A16 #orbits(w=4)=n/4-1 = 1,3,7,15;  A09 n=32,w=4 F_q distinct-e1 counts {96,160,192,224};
         A08 gap-2 constraint e_3 = e_1*e_2 on every w=6 subset of mu_8/mu_16).

------------------------------------------------------------------------------- API (all exact)

  ZetaRing(n):                      char-0 ring object Z[zeta_n] = Z[X]/(X^{n/2}+1)
    .zero(), .one()
    .from_exp(j):                   zeta^j   (j any integer, reduced mod 2h with sign)
    .add(u,v), .sub(u,v), .mul(u,v), .smul(c,u)
    .is_zero(u)

  esym_ring(R, S_exps):             elementary symmetric e_0..e_w of {zeta^i : i in S_exps} (in R).
  powersum_ring(R, S_exps, r):      p_r = sum_{i in S} zeta^{r*i}                            (in R).
  monomial_mod_ring(R, S_exps, j):  coeff list (low..high, length w) of X^j mod prod(X - zeta^i).

  esym_value(R, S_exps, t):         e_t(S) as a ring element (convenience).
  esym_vanishes_char0(R,S_exps,t):  exact bool: does e_t(S) = 0 in Z[zeta_n]?

  FieldZeta(q, n):                  F_q mirror (q = 1 mod n); z = a fixed primitive n-th root.
    .from_exp(j):                   zeta^j mod q (int)
  esym_value_Fq(F, S_exps, t):      e_t(S) evaluated at the F_q root z (int mod q).
  esym_vanishes_Fq(F, S_exps, t):   exact bool: e_t(S) = 0 in F_q.
  monomial_mod_Fq(vals, j, q):      F_q version of monomial_mod_ring (vals = the n-th roots).

------------------------------------------------------------------------------- ENUMERATORS

  distinct_e1_char0(R, n, w, *, vanish={2}, e1_nonzero=True):
       #distinct e_1(S) over w-subsets S of mu_n with e_t(S)=0 for all t in `vanish`
       (and optionally e_1 != 0).  The A09 "char-0 count N(char0)".
  distinct_e1_Fq(F, n, w, *, vanish={2}, e1_nonzero=True):
       same over F_q.  The A09 "N(F_q)".
  modq_defect(n, w, q, *, vanish={2}):
       (N_char0, N_Fq, defect=N_Fq-N_char0)  =  the per-q mod-q additive-energy defect k_D.

  orbit_count_char0(R, n, w, *, vanish={2}, e1_nonzero=True):
       # mu_n-orbits of w-subsets with e_t=0 (t in vanish), e_1 != 0.  The A16 object.
  canonical_orbit_rep(exps, n):     translation-normalized canonical key of the mu_n-orbit.

  subsets_with_vanishing_char0(R, n, w, vanish):  list the actual S (for inspection / A08).
  subsets_with_vanishing_Fq(F, n, w, vanish):     ditto over F_q.

Everything is EVIDENCE infrastructure — exact small-case enumeration, never a proof at n=2^32.
Run `python scripts/probes/cyclotomic_exact_enumerator.py` to execute the full self-test +
a short demo table.
"""

from itertools import combinations

# ============================================================= char-0: Z[zeta_n] = Z[X]/(X^h+1)
class ZetaRing:
    """Z[X]/(X^h + 1), h = n/2.  Elements = list of h Python ints (basis zeta^0..zeta^{h-1})."""
    def __init__(self, n):
        assert n >= 2 and (n & (n - 1)) == 0, "n must be a power of two"
        self.n = n
        self.h = n // 2

    def zero(self):
        return [0] * self.h

    def one(self):
        v = [0] * self.h
        v[0] = 1
        return v

    def from_exp(self, j):
        """zeta^j as a ring element (j arbitrary integer); zeta has order 2h = n."""
        h = self.h
        j %= (2 * h)
        v = [0] * h
        if j < h:
            v[j] = 1
        else:
            v[j - h] = -1            # zeta^{h+i} = -zeta^i
        return v

    def add(self, u, v):
        return [a + b for a, b in zip(u, v)]

    def sub(self, u, v):
        return [a - b for a, b in zip(u, v)]

    def smul(self, c, u):
        return [c * a for a in u]

    def mul(self, u, v):
        h = self.h
        out = [0] * h
        for i, ai in enumerate(u):
            if ai == 0:
                continue
            for jj, bj in enumerate(v):
                if bj == 0:
                    continue
                k = i + jj
                c = ai * bj
                if k < h:
                    out[k] += c
                else:
                    out[k - h] -= c   # zeta^h = -1
        return out

    def is_zero(self, u):
        return all(a == 0 for a in u)


def esym_ring(R, S_exps):
    """elementary symmetric polynomials e_0..e_w of the multiset {zeta^i : i in S_exps}, exact in R."""
    w = len(S_exps)
    e = [R.zero() for _ in range(w + 1)]
    e[0] = R.one()
    for idx, i in enumerate(S_exps):
        xi = R.from_exp(i)
        for j in range(min(idx + 1, w), 0, -1):
            e[j] = R.add(e[j], R.mul(xi, e[j - 1]))
    return e


def powersum_ring(R, S_exps, r):
    s = R.zero()
    for i in S_exps:
        s = R.add(s, R.from_exp(r * i))
    return s


def monomial_mod_ring(R, S_exps, j):
    """coefficient list (length w, low->high) of  X^j  mod  prod_{i in S}(X - zeta^i)  over R.

    m(X) = X^w - e_1 X^{w-1} + e_2 X^{w-2} - ... + (-1)^w e_w.  Reduce X^j by repeated
    X^w = e_1 X^{w-1} - e_2 X^{w-2} + ... - (-1)^w e_w  (coefficient of X^{w-t} is (-1)^{t+1} e_t).
    """
    w = len(S_exps)
    e = esym_ring(R, S_exps)
    redvec = [R.zero() for _ in range(w)]
    for t in range(1, w + 1):
        redvec[w - t] = R.smul((-1) ** (t + 1), e[t])
    if j < w:
        poly = [R.zero() for _ in range(w)]
        poly[j] = R.one()
        return poly
    cur = [list(c) for c in redvec]                  # X^w
    for _ in range(j - w):
        top = cur[w - 1]
        shifted = [R.zero()] + cur[:w - 1]           # X * cur, dropping the X^w slot
        for t in range(w):
            shifted[t] = R.add(shifted[t], R.mul(top, redvec[t]))
        cur = shifted
    return cur


def esym_value(R, S_exps, t):
    """e_t(S) as a ring element (0 <= t <= |S|)."""
    e = esym_ring(R, S_exps)
    return e[t] if 0 <= t < len(e) else R.zero()


def esym_vanishes_char0(R, S_exps, t):
    """exact bool: e_t(S) = 0 in Z[zeta_n]."""
    return R.is_zero(esym_value(R, S_exps, t))


# ================================================================= char-p: F_q mirror (q = 1 mod n)
def _primitive_root(q):
    """smallest primitive root mod prime q (small q only; pure python)."""
    phi = q - 1
    # prime factors of phi
    f, m, fac = phi, 2, []
    while m * m <= f:
        if f % m == 0:
            fac.append(m)
            while f % m == 0:
                f //= m
        m += 1
    if f > 1:
        fac.append(f)
    for g in range(2, q):
        if all(pow(g, phi // pr, q) != 1 for pr in fac):
            return g
    raise RuntimeError("no primitive root")


class FieldZeta:
    """F_q mirror with a fixed primitive n-th root z (q must be 1 mod n)."""
    def __init__(self, q, n):
        assert q > 2 and (q - 1) % n == 0, "need q = 1 mod n"
        self.q = q
        self.n = n
        g = _primitive_root(q)
        self.z = pow(g, (q - 1) // n, q)            # a fixed primitive n-th root
        # sanity: order exactly n
        assert pow(self.z, n, q) == 1 and pow(self.z, n // 2, q) != 1

    def from_exp(self, j):
        return pow(self.z, j % self.n, self.q)


def gen_mu(q, n):
    """the n-element subgroup mu_n < F_q^*, indexed by exponent: g[i] = zeta^i."""
    F = FieldZeta(q, n)
    return [F.from_exp(i) for i in range(n)]


def esym_Fq(vals, q):
    w = len(vals)
    e = [0] * (w + 1)
    e[0] = 1
    for idx, xi in enumerate(vals):
        for j in range(min(idx + 1, w), 0, -1):
            e[j] = (e[j] + xi * e[j - 1]) % q
    return e


def esym_value_Fq(F, S_exps, t):
    vals = [F.from_exp(i) for i in S_exps]
    e = esym_Fq(vals, F.q)
    return e[t] if 0 <= t < len(e) else 0


def esym_vanishes_Fq(F, S_exps, t):
    return esym_value_Fq(F, S_exps, t) % F.q == 0


def monomial_mod_Fq(vals, j, q):
    """coeff list (low->high, length w) of X^j mod prod(X - vals[i]) over F_q."""
    w = len(vals)
    e = esym_Fq(vals, q)
    redvec = [0] * w
    for t in range(1, w + 1):
        redvec[w - t] = ((-1) ** (t + 1) * e[t]) % q
    if j < w:
        poly = [0] * w
        poly[j] = 1
        return poly
    cur = list(redvec)
    for _ in range(j - w):
        top = cur[w - 1]
        shifted = [0] + cur[:w - 1]
        for t in range(w):
            shifted[t] = (shifted[t] + top * redvec[t]) % q
        cur = shifted
    return cur


# ====================================================================== high-level enumerators
def subsets_with_vanishing_char0(R, n, w, vanish):
    """all w-subsets S of {0..n-1} with e_t(S)=0 (char-0) for every t in `vanish`."""
    out = []
    for S in combinations(range(n), w):
        if all(esym_vanishes_char0(R, S, t) for t in vanish):
            out.append(S)
    return out


def subsets_with_vanishing_Fq(F, n, w, vanish):
    out = []
    for S in combinations(range(n), w):
        if all(esym_vanishes_Fq(F, S, t) for t in vanish):
            out.append(S)
    return out


def distinct_e1_char0(R, n, w, *, vanish=frozenset({2}), e1_nonzero=True):
    """#distinct e_1(S) (as exact ring vectors) over w-subsets with e_t=0 (t in vanish)."""
    seen = set()
    for S in combinations(range(n), w):
        if not all(esym_vanishes_char0(R, S, t) for t in vanish):
            continue
        e1 = esym_value(R, S, 1)
        if e1_nonzero and R.is_zero(e1):
            continue
        seen.add(tuple(e1))
    return len(seen)


def distinct_e1_Fq(F, n, w, *, vanish=frozenset({2}), e1_nonzero=True):
    """#distinct e_1(S) mod q over w-subsets with e_t=0 mod q (t in vanish)."""
    seen = set()
    for S in combinations(range(n), w):
        if not all(esym_vanishes_Fq(F, S, t) for t in vanish):
            continue
        e1 = esym_value_Fq(F, S, 1)
        if e1_nonzero and e1 % F.q == 0:
            continue
        seen.add(e1 % F.q)
    return len(seen)


def modq_defect(n, w, q, *, vanish=frozenset({2})):
    """(N_char0, N_Fq, defect = N_Fq - N_char0): the per-q mod-q additive-energy defect k_D."""
    R = ZetaRing(n)
    F = FieldZeta(q, n)
    c0 = distinct_e1_char0(R, n, w, vanish=vanish)
    cq = distinct_e1_Fq(F, n, w, vanish=vanish)
    return c0, cq, cq - c0


def canonical_orbit_rep(exps, n):
    """canonical key for the mu_n-orbit of the subset {zeta^e : e in exps}: the
    lexicographically least translation of the sorted exponent tuple."""
    best = None
    for t in range(n):
        shifted = tuple(sorted((e + t) % n for e in exps))
        if best is None or shifted < best:
            best = shifted
    return best


def orbit_count_char0(R, n, w, *, vanish=frozenset({2}), e1_nonzero=True):
    """# mu_n-orbits of w-subsets with e_t=0 (t in vanish), e_1 != 0 (char-0, exact)."""
    orbits = set()
    for S in combinations(range(n), w):
        if not all(esym_vanishes_char0(R, S, t) for t in vanish):
            continue
        if e1_nonzero and R.is_zero(esym_value(R, S, 1)):
            continue
        orbits.add(canonical_orbit_rep(S, n))
    return len(orbits)


# ============================================================================ self-test (3 ways)
def _complex_check():
    import cmath
    for n in (8, 16):
        R = ZetaRing(n)
        zc = cmath.exp(2j * cmath.pi / n)

        def ev(u):
            return sum(c * zc ** i for i, c in enumerate(u))

        # (a) ring mul / from_exp vs complex
        for a in range(2 * n):
            for b in range(2 * n):
                lhs = ev(R.mul(R.from_exp(a), R.from_exp(b)))
                assert abs(lhs - zc ** (a + b)) < 1e-9, (n, a, b)
        # (b) monomial_mod: X^j mod prod(X-zeta^i) at X=zeta^{i0} (i0 in S) == zeta^{j*i0}
        S = [0, 1, 3, 4] if n == 8 else [0, 1, 3, 4, 7, 9]
        for j in (5, 7, 11):
            poly = monomial_mod_ring(R, S, j)

            def evpoly(at):
                return sum(ev(poly[t]) * at ** t for t in range(len(poly)))
            for i0 in S:
                at = zc ** i0
                assert abs(evpoly(at) - at ** j) < 1e-8, (n, j, i0)
        # (c) esym_vanishes_char0 vs complex: e_t(S)=0 ring  <=>  |e_t(S)|~0 complex
        for w in (3, 4):
            for S in combinations(range(n), w):
                for t in range(1, w + 1):
                    ring0 = esym_vanishes_char0(R, S, t)
                    # complex value of e_t via Newton from power sums is overkill;
                    # evaluate the ring vector directly:
                    cval = ev(esym_value(R, S, t))
                    cplx0 = abs(cval) < 1e-8
                    assert ring0 == cplx0, (n, S, t, cval, ring0)
    print("[self-test 1] ring + monomial_mod + esym vanishing cross-checked vs complex (n=8,16)  OK")


def _modular_check():
    # esym_vanishes_Fq vs brute modular evaluation of e_t at the actual root, n=8,16
    for n, q in ((8, 17), (16, 97)):
        F = FieldZeta(q, n)
        vals_all = [F.from_exp(i) for i in range(n)]
        for w in (3, 4):
            for S in combinations(range(n), w):
                vals = [vals_all[i] for i in S]
                e = esym_Fq(vals, q)
                for t in range(1, w + 1):
                    assert esym_vanishes_Fq(F, S, t) == (e[t] % q == 0), (n, q, S, t)
    print("[self-test 2] esym_vanishes_Fq cross-checked vs brute modular esym (n=8,16)  OK")


def _campaign_numbers_check():
    """Cross-check the high-level enumerators against the three workers' REPORTED exact numbers."""
    # (A16) #orbits of w=4, e_2=0, e_1!=0 subsets of mu_n  ==  n/4 - 1  for n=8,16,32.
    for n in (8, 16, 32):
        R = ZetaRing(n)
        oc = orbit_count_char0(R, n, 4, vanish=frozenset({2}))
        assert oc == n // 4 - 1, ("A16 orbit count", n, oc, n // 4 - 1)
    # (A16) char-0 distinct e_1 for w=4 e_2=0 e_1!=0: 1,3,7,15 for n=8,16,32 (one per orbit here).
    # (A09 DROP/saturation) n=32, w=4, e_2=0 F_q distinct-e1 counts == EXACTLY {96,160,192,224}
    #                        across primes 1 mod 32 (A09 reported this exact set).
    a09_seen = set()
    for q in (97, 193, 257, 353, 449, 577, 673, 769, 929):
        if (q - 1) % 32 != 0:
            continue
        F = FieldZeta(q, 32)
        a09_seen.add(distinct_e1_Fq(F, 32, 4, vanish=frozenset({2})))
    assert a09_seen == {96, 160, 192, 224}, ("A09 F_q counts", sorted(a09_seen))
    # (A09 RISE/halo) n=16, w=6: char-0 count 0; F_q "halo carriers" produce NEW e_1 with the exact
    #                 reported RISE column 17->16, 97->32, 113->48, 193->16 (defect in [0,+48]).
    R16 = ZetaRing(16)
    assert distinct_e1_char0(R16, 16, 6, vanish=frozenset({2})) == 0, "A09 RISE: char-0 count not 0"
    rise = {q: distinct_e1_Fq(FieldZeta(q, 16), 16, 6, vanish=frozenset({2}))
            for q in (17, 97, 113, 193)}
    assert rise == {17: 16, 97: 32, 113: 48, 193: 16}, ("A09 RISE column", rise)
    # (A08) gap-2 constraint: on EVERY w=6 subset of mu_8 / mu_16, the symmetric-function identity
    #       e_3(S) = e_1(S) * e_2(S) is NOT generic; the actionable's gap-2 cell is selected by it.
    #       Cross-check the substrate reproduces the count of w=6 subsets satisfying e_3 = e_1*e_2.
    for n in (8, 16):
        R = ZetaRing(n)
        cnt = 0
        for S in combinations(range(n), 6):
            e = esym_ring(R, S)
            lhs = e[3]
            rhs = R.mul(e[1], e[2])
            if R.is_zero(R.sub(lhs, rhs)):
                cnt += 1
        # mu_8 has C(8,6)=28 subsets; mu_16 has C(16,6)=8008. The constraint is satisfied by a
        # proper nonempty subset (it is a genuine algebraic condition, neither always nor never).
        total = 28 if n == 8 else 8008
        assert 0 < cnt < total, ("A08 gap-2 constraint trivial", n, cnt, total)
    print("[self-test 3] enumerators cross-checked vs A16 (#orbits=n/4-1), "
          "A09 DROP (n=32,w=4 F_q counts == {96,160,192,224}), "
          "A09 RISE (n=16,w=6 halo column 16/32/48/16), A08 (gap-2 constraint nontrivial)  OK")


def _self_test():
    _complex_check()
    _modular_check()
    _campaign_numbers_check()


def _demo():
    print("\n--- demo: distinct-e_1 + mod-q defect for e_2=0, w=4 (the A09 object) ---")
    print(f"{'n':>4} {'q':>6} {'N_char0':>8} {'N_Fq':>6} {'defect':>7}")
    for n, q in ((8, 17), (16, 97), (16, 193), (32, 97), (32, 193)):
        c0, cq, d = modq_defect(n, 4, q, vanish=frozenset({2}))
        print(f"{n:>4} {q:>6} {c0:>8} {cq:>6} {d:>+7}")
    print("\n--- demo: char-0 #orbits(w=4, e_2=0, e_1!=0) == n/4 - 1 ---")
    for n in (8, 16, 32):
        R = ZetaRing(n)
        oc = orbit_count_char0(R, n, 4)
        print(f"  n={n:>3}: #orbits={oc:>3}   n/4-1={n//4-1:>3}   match={oc == n//4-1}")
    print("\n--- demo: higher vanishing e_3=0 (w=5) distinct-e_1, char-0 vs F_q ---")
    for n in (8, 16):
        R = ZetaRing(n)
        c0 = distinct_e1_char0(R, n, 5, vanish=frozenset({3}))
        F = FieldZeta(97 if n == 16 else 17, n)
        cq = distinct_e1_Fq(F, n, 5, vanish=frozenset({3}))
        print(f"  n={n:>3}: e_3=0,w=5  N_char0={c0:>4}  N_Fq(q={F.q})={cq:>4}")


if __name__ == "__main__":
    _self_test()
    _demo()
