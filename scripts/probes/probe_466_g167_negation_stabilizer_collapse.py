#!/usr/bin/env python3
"""
#466 G167 — negation-stabilizer collapse probe (reproducible).

Verifies, by exact enumeration over small primes, the structural theorem formalized in
`Frontier/_G167NegationStabilizerCollapse.lean`:

  In F_p^*, a MINIMAL zero-sum support S that is invariant under negation (S = -S) has |S| = 2,
  and is exactly {x, -x}.

Consequences confirmed here:
  * every negation-symmetric minimal zero-sum support has size exactly 2 (the accident sector);
  * for support sizes s != 2 no minimal support is negation-symmetric, so the order-2 scaling -1
    (and hence any 2-power scaling group containing it) acts FIXED-POINT-FREELY, giving 2 | N_s and,
    for the full cyclic 2-Sylow H of order 2^k, 2^k | N_s for s != 2.

Also verifies the key algebraic input: the sum over any nontrivial subgroup of F_p^* is 0 mod p.
"""
from itertools import combinations


def prim_root(p: int) -> int:
    n = p - 1
    for g in range(2, p):
        seen, x = set(), 1
        for _ in range(n):
            x = (x * g) % p
            seen.add(x)
        if len(seen) == n:
            return g
    raise ValueError(f"no primitive root for {p}")


def subgroup(p: int, g: int, order: int):
    assert (p - 1) % order == 0
    h = pow(g, (p - 1) // order, p)
    out, x = [], 1
    for _ in range(order):
        out.append(x)
        x = (x * h) % p
    return out


def minimal_zero_sum_supports(p: int, s: int):
    res = []
    for c in combinations(range(1, p), s):
        if sum(c) % p != 0:
            continue
        minimal = True
        for t in range(1, s):
            broke = False
            for sub in combinations(c, t):
                if sum(sub) % p == 0:
                    minimal = False
                    broke = True
                    break
            if broke:
                break
        if minimal:
            res.append(frozenset(c))
    return res


def main() -> None:
    ok = True
    for p, smax in [(17, 6), (41, 5), (97, 5)]:
        g = prim_root(p)
        n = p - 1
        # (algebraic input) sum over every nontrivial subgroup is 0
        for d in range(2, n + 1):
            if n % d == 0 and sum(subgroup(p, g, d)) % p != 0:
                ok = False
                print(f"  FAIL p={p}: subgroup of order {d} has nonzero sum")
        k, m = 0, n
        while m % 2 == 0:
            m //= 2
            k += 1
        print(f"p={p}: primitive root {g}, 2-Sylow order 2^{k}={2 ** k}")
        for s in range(2, smax + 1):
            M = minimal_zero_sum_supports(p, s)
            symm = [S for S in M if frozenset((-x) % p for x in S) == S]
            symm_sizes = {len(S) for S in symm}
            div = (len(M) % (2 ** k) == 0)
            # theorem: all symmetric minimal supports have size 2
            if any(sz != 2 for sz in symm_sizes):
                ok = False
                print(f"  FAIL s={s}: symmetric support of size != 2")
            if s != 2 and symm:
                ok = False
                print(f"  FAIL s={s}: a size-{s} minimal support is negation-symmetric")
            if s != 2 and not div:
                ok = False
                print(f"  FAIL s={s}: |MZS_s|={len(M)} not divisible by 2^{k}")
            print(f"    s={s}: |MZS|={len(M)}  symmetric={len(symm)}"
                  f"  (sizes {symm_sizes or '∅'})  2^{k}|N_s={div}")
    print("PASS" if ok else "FAIL")
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
