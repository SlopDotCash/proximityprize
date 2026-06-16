#!/usr/bin/env python3
"""
probe_444_singleton_fiber_scaling.py  (#444 "CRACK D" — the non-symmetric tower recursion)

GOAL: measure s(S) = number of SINGLETON FIBERS of each list-codeword's agreement set S,
for the worst-case window word, across growing n = 2^mu. The squaring map
  sigma : mu_n -> mu_{n/2},  x |-> x^2   (2-to-1, fibers {x,-x})
decomposes S by fibers: each fiber {x,-x} contributes 0, 1, or 2 points to S.
  - "double" fibers (both x,-x in S)  -> captured by the symmetric e_{2l}(+-z) tower
  - "singleton" fibers (exactly one)  -> the NON-symmetric defect; s(S) := # singletons.
A z->-z symmetric S has s(S)=0. The dossier claim under test:

  CONJECTURE (task #4): the worst window word has s(S) = O(1) (a constant kappa,
  independent of n), so the tower recursion applies up to an O(1) correction and the
  worst-case list is constant in n.

We test this DIRECTLY: for the worst word at each (n, rho), report
  - L                : worst-case list size
  - max_s, mean_s    : max / mean singleton-fiber count over the list codewords
  - sym_count        : # codewords with s(S)=0 (symmetric, tower-captured)
  - and for the CONSECUTIVE word x^{a-1}(1+x) specifically: its s(S) profile,
    since (1+x) has a clean even/odd structure 1+(-x)=1-x (the dossier worst at rho<1/4).

Also reports the descent invariant a = 2|B| + |O1| where |O1| = s(S) is the singleton
count and |B| = #double fibers, to confirm the DescentKernelLemma bookkeeping:
agreement a = 2*(#double fibers) + (#singleton fibers).

Exact arithmetic mod p, multiple prize-shaped primes, proper subgroups (never n=p-1).
"""
import itertools, sys
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta)
    base = target - (target % n) + 1
    p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n

def subgroup(n, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)
    elts, x = [], 1
    for _ in range(n):
        elts.append(x); x = (x * zeta) % p
    assert len(set(elts)) == n
    return elts, zeta

def neg_index_map(elts, p):
    pos = {v: i for i, v in enumerate(elts)}
    return [pos[(p - v) % p] for v in elts]

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def poly_coeffs(xs, ys, p):
    k = len(xs)
    coeffs = [0] * k
    for i in range(k):
        num, den = [1], 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
        scale = (ys[i] * pow(den, p - 2, p)) % p
        for t in range(len(num)):
            coeffs[t] = (coeffs[t] + scale * num[t]) % p
    return tuple(coeffs)

def eval_poly(coeffs, x, p):
    v = 0
    for c in reversed(coeffs):
        v = (v * x + c) % p
    return v

def full_list(uvals, elts, k, s, p):
    n = len(elts)
    idxs = list(range(n))
    seen = {}
    for T in itertools.combinations(idxs, k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = poly_coeffs(xs, ys, p)
        if c in seen: continue
        agree = tuple(i for i in idxs if eval_poly(c, elts[i], p) == uvals[i])
        if len(agree) >= s:
            seen[c] = agree
    return seen

def fiber_profile(agree, neg):
    """returns (num_double, num_singleton): #fibers {i,neg[i]} fully in S vs exactly one in S."""
    aset = set(agree)
    seen_fibers = set()
    doubles = singles = 0
    for i in agree:
        f = frozenset((i, neg[i]))
        if f in seen_fibers: continue
        seen_fibers.add(f)
        cnt = (1 if i in aset else 0) + (1 if neg[i] in aset else 0)
        if cnt == 2: doubles += 1
        else: singles += 1
    return doubles, singles

def word_consecutive(elts, a, p):
    return [(pow(x, a, p) + pow(x, a - 1, p)) % p for x in elts]

def word_two_exp(elts, a, b, p):
    return [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]

def run(n, beta=4.0, rhos=(0.25, 0.125)):
    print(f"\n========== n={n} (mu={n.bit_length()-1}) ==========")
    p = find_window_prime(n, beta)
    elts, zeta = subgroup(n, p)
    neg = neg_index_map(elts, p)
    m = (p - 1) // n
    print(f"  p={p}  m=(p-1)/n={m}")
    for rho in rhos:
        k = max(1, round(rho * n))
        if k >= n: continue
        eta = rho
        s = round((rho + eta) * n)
        if s < k: s = k
        if s > n: continue
        # build candidate words
        cands = {}
        for a in range(2, n):
            cands[f"x^{a}+x^{a-1}"] = ("consec", a, word_consecutive(elts, a, p))
        for a in range(1, n, 2):
            for b in range(a + 2, n, 2):
                cands[f"x^{a}+x^{b}(odd)"] = ("twoexp", a, word_two_exp(elts, a, b, p))
        # find worst word by list size
        worst = (-1, None, None, None)
        for name, (kind, a, uv) in cands.items():
            lst = full_list(uv, elts, k, s, p)
            if len(lst) > worst[0]:
                worst = (len(lst), name, lst, kind)
        L, wname, wlist, wkind = worst
        # singleton-fiber profile over the worst word's list
        prof = [fiber_profile(ag, neg) for ag in wlist.values()]
        s_counts = [si for (_, si) in prof]
        d_counts = [di for (di, _) in prof]
        max_s = max(s_counts) if s_counts else 0
        mean_s = sum(s_counts) / len(s_counts) if s_counts else 0.0
        sym = sum(1 for si in s_counts if si == 0)
        # confirm a = 2|B| + |O1| for each codeword
        ok = all(2 * di + si == len(ag) for (di, si), ag in zip(prof, wlist.values()))
        print(f"    rho={rho:.4f} k={k} s={s}: WORST L={L} [{wname}]  "
              f"s(S): max={max_s} mean={mean_s:.2f}  sym(s=0)={sym}/{L}  "
              f"a=2|B|+|O1|? {ok}")
        # also: the consecutive a=2 word specifically (x^2+x = x(1+x)), the dossier worst
        if "x^2+x^1" in cands:
            uv2 = cands["x^2+x^1"][2]
            l2 = full_list(uv2, elts, k, s, p)
            prof2 = [fiber_profile(ag, neg) for ag in l2.values()]
            sc2 = [si for (_, si) in prof2]
            print(f"      consec a=2 [x(1+x)]: L={len(l2)}  s(S) per cw = {sorted(sc2)}")

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [8, 16, 32]
    for n in ns:
        run(n)
