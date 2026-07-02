#!/usr/bin/env python3
"""#466 lane W1 (B2): does plain RS satisfy [GG25] Def 3.1 (curve decodability) at small n?

[GG25] Def 3.1 / [Jo26] Def 2.7: C is (l, delta, a, b)-curve-decodable if for every stack
u = (u_0..u_l) and codeword-valued f : F_q -> C, whenever the close set
A = {alpha : dist(sum_j alpha^j u_j, f(alpha)) <= delta*n} has >= a seeds, some single
codeword curve (c_0..c_l) explains f on >= b seeds of A (f(alpha) = sum_j alpha^j c_j).

The nontrivial regime is b > l+1 (b <= l+1 is free by interpolation, [Jo26] Lemma 5.2).
We take l = 1 (lines of codewords), b = 3, and hunt COUNTERMODELS for plain RS:

  adversary picks a stack u, computes per-seed close lists
  L_alpha = {c in RS : agree(c, u_0 + alpha*u_1) >= n - D}, then chooses f(alpha) in L_alpha
  in "arc position" (no 3 chosen points on a common codeword line). If that succeeds with
  |closeSet| = s, then RS is NOT (1, D/n, a, 3)-curve-decodable for ANY a <= s.

Method notes:
  * close lists via interpolation through k-subsets of agreement positions (never enumerate
    q^k codewords): any codeword agreeing on >= n-D >= k positions is determined by k of them.
  * the line through two chosen points (al, f_al), (be, f_be) is c1 = (f_al-f_be)/(al-be),
    c0 = f_al - al*c1 (automatically codewords); a third point is on it iff value matches.
    So the adversary's task is an arc (no-3-collinear) selection in the fibered product,
    done by exact DFS with backtracking.
  * closeSet == chosen S exactly: off S the lists are empty, so no value of f is close there.

REGIME FLAGS (honest): this is a combinatorial scale-model, NOT a character-sum probe;
q = 17/41 (n=8), 97 (n=16) violate p >= n^4 (they are small-q scale models); domain = mu_n a
PROPER subgroup, p = 1 mod n, multiple primes. n = 8 with q = 17 has q-1 = 2n (flagged:
correlated with X^{n/2} structure); q = 41, 97 do not.

Contrast: the same hunt is run below Johnson (expect: forced f / tiny close sets, no
countermodel of the same shape) and in-window (expect: countermodel).
"""

import itertools
import random
import sys
from math import isqrt

random.seed(466)


def make_field(p):
    inv = [0] * p
    for x in range(1, p):
        inv[x] = pow(x, p - 2, p)
    return inv


def subgroup(p, n):
    # find generator of F_p^*
    def is_gen(g):
        seen = set()
        x = 1
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        return len(seen) == p - 1
    g = next(g for g in range(2, p) if is_gen(g))
    h = pow(g, (p - 1) // n, p)
    dom = []
    x = 1
    for _ in range(n):
        dom.append(x)
        x = x * h % p
    assert len(set(dom)) == n
    return dom


def interpolate(p, inv, pts, k):
    """Lagrange coefficients not needed; return the evaluation on full domain of the
    unique deg<k poly through pts = [(x_i, y_i)] (len k), evaluated at x (list)."""
    def ev(x):
        tot = 0
        for i, (xi, yi) in enumerate(pts):
            num, den = 1, 1
            for j, (xj, _) in enumerate(pts):
                if i == j:
                    continue
                num = num * ((x - xj) % p) % p
                den = den * ((xi - xj) % p) % p
            tot = (tot + yi * num * inv[den]) % p
        return tot
    return ev


def close_list(p, inv, dom, k, w, agree_min):
    """All RS[dom,k] codewords agreeing with word w on >= agree_min positions."""
    n = len(dom)
    found = {}
    for pos in itertools.combinations(range(n), k):
        pts = [(dom[i], w[i]) for i in pos]
        ev = interpolate(p, inv, pts, k)
        cw = tuple(ev(x) for x in dom)
        ag = sum(1 for i in range(n) if cw[i] == w[i])
        if ag >= agree_min:
            found[cw] = ag
    return list(found.keys())


def arc_dfs(p, inv, seeds, lists, limit=400000):
    """Choose f(alpha) in lists[alpha] with no 3 points on a common codeword line.
    Returns assignment dict or None. Exact DFS with a step budget."""
    order = sorted(seeds, key=lambda a: len(lists[a]))
    chosen = []  # (alpha, value tuple)
    assign = {}
    steps = [0]

    def value_on_line(a1, v1, a2, v2, a3):
        # c1 = (v1-v2)/(a1-a2), value at a3 = v1 + (a3-a1)*c1 (componentwise)
        d = inv[(a1 - a2) % p]
        return tuple((v1[i] + (a3 - a1) * ((v1[i] - v2[i]) * d % p)) % p
                     for i in range(len(v1)))

    def ok(alpha, v):
        for (b1, w1), (b2, w2) in itertools.combinations(chosen, 2):
            if value_on_line(b1, w1, b2, w2, alpha) == v:
                return False
        return True

    def rec(idx):
        steps[0] += 1
        if steps[0] > limit:
            return False
        if idx == len(order):
            return True
        alpha = order[idx]
        for v in lists[alpha]:
            if ok(alpha, v):
                chosen.append((alpha, v))
                assign[alpha] = v
                if rec(idx + 1):
                    return True
                chosen.pop()
                del assign[alpha]
        return False

    if rec(0):
        return dict(assign)
    return None


def max_fiber(p, inv, assign):
    """Max number of chosen points on a single codeword line (verification)."""
    pts = list(assign.items())
    best = 0
    if len(pts) < 2:
        return len(pts)
    for (a1, v1), (a2, v2) in itertools.combinations(pts, 2):
        d = inv[(a1 - a2) % p]
        c1 = tuple((v1[i] - v2[i]) * d % p for i in range(len(v1)))
        cnt = 0
        for (a3, v3) in pts:
            if all((v1[i] + (a3 - a1) * c1[i]) % p == v3[i] for i in range(len(v1))):
                cnt += 1
        best = max(best, cnt)
    return best


def run_config(p, n, k, trials=6):
    inv = make_field(p)
    dom = subgroup(p, n)
    johnson = 1 - (k / n) ** 0.5
    print(f"\n=== q={p}, n={n}, k={k} (rho={k/n}), domain=mu_{n}, l=1, b=3 ===")
    print(f"    Johnson 1-sqrt(rho)={johnson:.3f}, capacity 1-rho={1-k/n:.3f}, "
          f"UDR floor (n-k)/(2n)={(n-k)/(2*n):.3f}")
    for D in range(1, n - k + 1):
        delta = D / n
        agree_min = n - D
        regime = ("UDR/sub-Johnson" if delta < johnson else
                  ("WINDOW (Johnson,capacity)" if delta < 1 - k / n else "at/above capacity"))
        results = []
        for t in range(trials):
            if t < trials - 2:
                u0 = [random.randrange(p) for _ in range(n)]
                u1 = [random.randrange(p) for _ in range(n)]
                kind = "rand"
            elif t == trials - 2:
                # structured: u1 a codeword, u0 random
                ev = interpolate(p, inv, [(dom[i], random.randrange(p)) for i in range(k)], k)
                u1 = [ev(x) for x in dom]
                u0 = [random.randrange(p) for _ in range(n)]
                kind = "u1=cw"
            else:
                # structured: both rows = codeword + few errors (close-to-code stack)
                def noisy():
                    ev = interpolate(p, inv,
                                     [(dom[i], random.randrange(p)) for i in range(k)], k)
                    w = [ev(x) for x in dom]
                    for i in random.sample(range(n), min(D, n)):
                        w[i] = random.randrange(p)
                    return w
                u0, u1 = noisy(), noisy()
                kind = "noisy-cw"
            lists = {}
            for alpha in range(p):
                w = [(u0[i] + alpha * u1[i]) % p for i in range(n)]
                L = close_list(p, inv, dom, k, w, agree_min)
                if L:
                    lists[alpha] = L
            S = set(lists)
            if len(S) < 3:
                results.append((kind, len(S), None, "close set <3 (b=3 unreachable)"))
                continue
            assign = arc_dfs(p, inv, S, lists)
            if assign is not None:
                mf = max_fiber(p, inv, assign)
                assert mf <= 2, "arc verification failed"
                results.append((kind, len(S), mf,
                                f"COUNTERMODEL: not (1,{D}/{n},a,3)-curve-dec for all a<={len(S)}"))
            else:
                results.append((kind, len(S), None, "no arc found (DFS exhausted/budget)"))
        smax = max(r[1] for r in results)
        cms = sum(1 for r in results if r[2] is not None)
        print(f"  D={D} (delta={delta:.3f}, {regime}): |closeSet| max={smax}, "
              f"countermodels {cms}/{len(results)}")
        for kind, s, mf, msg in results:
            print(f"      [{kind:9s}] |S|={s:3d} -> {msg}")


if __name__ == "__main__":
    # n=8: two primes (17 flagged q-1=2n; 41 clean), k=2 -> window (0.5, 0.75)
    run_config(17, 8, 2)
    run_config(41, 8, 2)
    # n=16, k=4 -> window (0.5, 0.75)
    run_config(97, 16, 4, trials=4)
    print("\nDone. Interpretation: a countermodel line means the adversary placed f-values on")
    print("the close lists in arc position, so NO codeword line explains 3 close seeds --")
    print("plain RS fails Def 3.1 there for every a up to the printed |S| (with b=3=l+2).")
