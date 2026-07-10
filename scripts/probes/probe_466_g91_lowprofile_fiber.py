#!/usr/bin/env python3
"""G91 probe: low-profile exact-appearance fiber bound D(t) <= C(s, a-t).

Claim under test (before Lean formalization):
  On a line (u0, u1) over RS[dom, k] with agreement threshold a, for any
  S subseteq Z(u1) with |S| = t < a, IF no NONZERO codeword vanishing on S
  agrees with u1 on >= a coordinates ("S-vanishing-far direction"), THEN
    D(S) := #{c in RS_k : c appears on the line with agreement >= a at some
              gamma, and zeroAgreement(c, u0, u1) == S}  <=  C(s, a-t),
  where s = |support(u1)|, z = |Z(u1)|, q-free.

Mechanism: each incidence (gamma, c) with exact profile S owns a private
(a-t)-subset of support(u1).

Also measured: the dichotomy failure branch (some nonzero codeword vanishing
on S agrees with u1 on >= a points), tightness of C(s,a-t), and comparison
with the field-power envelope q^(k-t).
"""

import itertools, random
from math import comb

Q = 17
N = 8
K = 2
A = 4
random.seed(466)

F = list(range(Q))
DOM = list(range(N))  # first N field elements as evaluation points

def poly_eval(coeffs, x):
    v = 0
    for c in reversed(coeffs):
        v = (v * x + c) % Q
    return v

# all RS[N, K] codewords (deg < K)
CODEWORDS = []
for coeffs in itertools.product(range(Q), repeat=K):
    CODEWORDS.append(tuple(poly_eval(coeffs, x) for x in DOM))
CODEWORDS = list(dict.fromkeys(CODEWORDS))
assert len(CODEWORDS) == Q ** K
ZERO = tuple([0] * N)

def agree(u, v):
    return sum(1 for i in range(N) if u[i] == v[i])

def line_word(u0, u1, g):
    return tuple((u0[i] + g * u1[i]) % Q for i in range(N))

def zero_set(u1):
    return frozenset(i for i in range(N) if u1[i] == 0)

def zero_agreement(c, u0, Z):
    return frozenset(i for i in Z if c[i] == u0[i])

def appearing(u0, u1):
    """codewords appearing with agreement >= A at some gamma (with witness g)."""
    out = {}
    for c in CODEWORDS:
        for g in F:
            if agree(c, line_word(u0, u1, g)) >= A:
                out.setdefault(c, []).append(g)
    return out

def s_vanishing_far(u1, S):
    """no nonzero codeword vanishing on S agrees with u1 on >= A coords."""
    for c in CODEWORDS:
        if c == ZERO:
            continue
        if all(c[i] == 0 for i in S) and agree(c, u1) >= A:
            return False
    return True

def zero_direction_safe(u0, u1, Z):
    for c in CODEWORDS:
        if len(zero_agreement(c, u0, Z)) >= A:
            return False
    return True

def run_line(u0, u1, stats):
    Z = zero_set(u1)
    z, s = len(Z), N - len(Z)
    if z < A:
        return
    safe = zero_direction_safe(u0, u1, Z)
    app = appearing(u0, u1)
    # bucket appearing codewords by exact zero-agreement profile
    fiber = {}
    for c in app:
        fiber.setdefault(zero_agreement(c, u0, Z), set()).add(c)
    for t in range(0, A):
        bound = comb(s, A - t)
        for S in itertools.combinations(sorted(Z), t):
            Sf = frozenset(S)
            D = len(fiber.get(Sf, ()))
            far = s_vanishing_far(u1, Sf)
            key = (t, s)
            if far:
                stats['checked'] += 1
                stats.setdefault('maxratio', {})
                if D > bound:
                    stats['violations'].append((u0, u1, S, D, bound, safe))
                if D > 0:
                    stats['nonempty_far'] += 1
                    m = stats['maxratio'].get(key, (0, 0, 0))
                    if D > m[0]:
                        stats['maxratio'][key] = (D, bound, Q ** (K - t))
            else:
                stats['far_fail'] += 1
                if D > 0:
                    stats['nonempty_notfar'] += 1
                    stats['max_D_notfar'] = max(stats.get('max_D_notfar', 0), D)

stats = {'checked': 0, 'violations': [], 'nonempty_far': 0,
         'far_fail': 0, 'nonempty_notfar': 0}

# directions: supports of sizes 1..4 with random nonzero values; offsets random
lines = 0
for s_target in (1, 2, 3, 4):
    for trial in range(30):
        supp = random.sample(range(N), s_target)
        u1 = [0] * N
        for i in supp:
            u1[i] = random.randrange(1, Q)
        u1 = tuple(u1)
        for _ in range(4):
            u0 = tuple(random.randrange(Q) for _ in range(N))
            run_line(u0, u1, stats)
            lines += 1
        # adversarial offsets: u0 = codeword + sparse noise (dense fibers)
        for _ in range(4):
            c = random.choice(CODEWORDS)
            u0 = list(c)
            for i in random.sample(range(N), 3):
                u0[i] = random.randrange(Q)
            run_line(tuple(u0), u1, stats)
            lines += 1

# also structured: u1 = indicator-type (census refuter shape) to exercise far-fail
for a_zeros in (4, 5, 6):
    u1 = tuple(0 if i < a_zeros else 1 for i in range(N))
    for _ in range(6):
        u0 = tuple(random.randrange(Q) for _ in range(N))
        run_line(u0, u1, stats)
        lines += 1

print(f"lines run: {lines}")
print(f"(S,t) instances with S-vanishing-far direction checked: {stats['checked']}")
print(f"  violations of D <= C(s, a-t): {len(stats['violations'])}")
print(f"  nonempty fibers among far instances: {stats['nonempty_far']}")
print(f"(S,t) instances where far FAILS (dichotomy other branch): {stats['far_fail']}")
print(f"  nonempty fibers there: {stats['nonempty_notfar']}, max D = {stats.get('max_D_notfar', 0)}")
print("\nmax realized D per (t, s) on far instances  [D, bound C(s,a-t), q^(k-t)]:")
for key in sorted(stats['maxratio']):
    D, b, fp = stats['maxratio'][key]
    print(f"  t={key[0]} s={key[1]}: D={D}  C(s,a-t)={b}  fieldpow={fp}")
if stats['violations']:
    print("\nVIOLATIONS:")
    for v in stats['violations'][:5]:
        print(v)
