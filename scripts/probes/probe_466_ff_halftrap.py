#!/usr/bin/env python3
"""
probe_466_ff_halftrap.py -- Lane W4 supplement (#466): the 2-power HALF-TRAP theorem
that closes the last corner of the function-field residue-ring model.

Context: probe_466_function_field.py established (A1) the trace-collapse degeneracy
(E != F_p(mu_n) => M = n exactly) and (A2/A3) that generating instances follow the
same empirical law as F_p. This supplement proves/verifies the remaining scoping fact:

  THEOREM (half-trap; elementary). Let n = 2^kappa >= 16 and let p be an odd prime
  with k = ord_n(p) >= 4 (so E = F_p(mu_n) = F_{p^k} is a "genuinely function-field-
  shaped" residue domain, deg f = k >= 4). Then:
    (i)  k is a 2-power, and p^{k/2} == n/2 + 1 (mod n) -- because squares in
         (Z/2^kappa)^* are exactly the units == 1 mod 8, and the ONLY order-2 unit
         == 1 mod 8 is 2^{kappa-1}+1;
    (ii) hence mu_n ∩ F_{p^{k/2}} = mu_{n/2}: HALF the subgroup lies in the
         half-degree subfield;
    (iii) choosing psi_a with a != 0 in ker(Tr_{E/F_{p^{k/2}}}) (an averaging argument
         over the p^{k/2}-element kernel) gives
              M_E(mu_n) >= n/2 - (n/2)/(p^{k/2}-1).
  Consequence: for n > 8 ln m (e.g. n >= 256 at beta ~ 4..5), n/2 > sqrt(2 n ln m):
  the prize-shaped law is FALSE at EVERY generating instance with k >= 4. The only
  residue-ring models that can carry the law are k = 1 (literally F_p) and k = 2 with
  p mod n in {n-1, n/2-1} (the two clean order-2 classes; p == -1 mod n is the
  norm-one-torus / generalized-Fermat-correlated class, flagged).

  So NO genuinely function-field-shaped (deg f >= 4... in fact >= 3 is impossible:
  ord must be a 2-power) residue model of the thin 2-power prize law exists.
  (deg f = 3: ord_n(p) = 3 never divides lambda(2^kappa) = 2^{kappa-2} -- impossible.)

S1 verifies (i)+(ii) by full census over (Z/2^kappa)^*, kappa = 4..12.
S2 verifies (iii) numerically at n = 256, k = 4, p in {577, 1087, 2111}:
   the exact sup over the trace-kernel characters (a 2D FFT over F_p^2) exceeds
   n/2 = 128 > sqrt(2 n ln m) = law bound -- an EXACT numerical law violation at a
   generating (non-degenerate) instance.

REGIME: mu_n proper, Q = p^4 >= n^4 (beta 4.6..5.5), multiple primes, no Fermat
primes, p == 63/65 mod 256 forced by (i) (ord-4 residues are the 4 sqrt's of 129).
"""

import math

import numpy as np

from probe_466_function_field import GFpk, is_prime, mult_order

OUT = []


def log(s=""):
    print(s, flush=True)
    OUT.append(str(s))


# ------------------------------------------------------------------ S1
def part_S1():
    log("=" * 78)
    log("S1 -- census over (Z/2^kappa)^*, kappa = 4..12: for every unit q of order")
    log("     k >= 4, verify q^{k/2} == 2^{kappa-1}+1 (=> mu_{n/2} subfield-trapped),")
    log("     and that order-2 units split clean/trapped exactly as {-1, n/2-1} / {n/2+1}.")
    log("=" * 78)
    all_ok = True
    for kappa in range(4, 13):
        n = 1 << kappa
        viol = 0
        n_dge4 = 0
        d2 = {}
        for q in range(3, n, 2):
            k = mult_order(q, n)
            if k == 1:
                continue
            if k >= 4:
                n_dge4 += 1
                if pow(q, k // 2, n) != n // 2 + 1:
                    viol += 1
            else:
                trapped = math.gcd(n, q - 1)
                d2.setdefault(trapped, []).append(q)
        clean = sorted(d2.get(2, []))
        ok = (viol == 0) and (clean == [n // 2 - 1, n - 1])
        all_ok &= ok
        log(f"  kappa={kappa:2d} n={n:5d}: order>=4 units: {n_dge4:5d}, "
            f"half-trap violations: {viol}; order-2 clean classes {clean} "
            f"== [n/2-1, n-1]: {ok}")
    log(f"  S1 THEOREM CENSUS: {'ALL CONFIRMED' if all_ok else 'VIOLATION FOUND'}")
    log("")
    return all_ok


# ------------------------------------------------------------------ S2
def part_S2(p, n=256):
    k = 4
    assert is_prime(p) and mult_order(p, n) == k, (p, n)
    K = GFpk(p, k)
    Q = K.Q
    assert (Q - 1) % n == 0
    m = (Q - 1) // n
    beta = math.log(Q) / math.log(n)
    log("-" * 78)
    log(f"S2 -- n = {n}, p = {p} (p mod {n} = {p % n}, ord = 4), E = F_p^4, "
        f"Q = {Q:.3e}, index m = {m:.3e}, beta = {beta:.2f}")
    log("-" * 78)

    one = tuple([1] + [0] * (k - 1))
    zeta = K.pw(K.g, (Q - 1) // n)
    pts, x = [], one
    for _ in range(n):
        x = K.mul(x, zeta)
        pts.append(x)
    assert x == one and len(set(pts)) == n

    # half-trap membership check: mu_{n/2} = squares of mu_n should satisfy y^{p^2} = y
    def frob2(y):
        return K.pw(y, p * p)

    sq = {K.mul(y, y) for y in pts}
    in_sub = all(frob2(y) == y for y in sq)
    odd_out = all(frob2(y) != y for y in pts if y not in sq)
    log(f"  mu_{n//2} (squares) inside F_p^2: {in_sub}; "
        f"odd-part outside F_p^2: {odd_out}   [(ii) CONFIRMED]")

    # trace to F_p and the relative-trace kernel basis
    def tr_abs(y):
        s, t = (0,) * k, y
        for _ in range(k):
            s = tuple((si + ti) % p for si, ti in zip(s, t))
            t = K.pw(t, p)
        assert all(c == 0 for c in s[1:])
        return s[0]

    # ker(Tr_{E/F'}) with F' = F_{p^2}: y + y^{p^2} = 0, an F_p-space of dim 2.
    # Solve on the basis u^i via Gaussian elimination mod p.
    cols = []
    for i in range(k):
        e = tuple(1 if j == i else 0 for j in range(k))
        img = tuple((a + b) % p for a, b in zip(e, frob2(e)))
        cols.append(img)
    # kernel of the k x k matrix whose i-th column is cols[i]
    M = [[cols[j][i] for j in range(k)] for i in range(k)]  # rows
    # Gauss over F_p, track combinations
    aug = [list(M[i]) for i in range(k)]
    piv_col_of_row = []
    r = 0
    piv_cols = []
    for c in range(k):
        pr = next((i for i in range(r, k) if aug[i][c] % p != 0), None)
        if pr is None:
            continue
        aug[r], aug[pr] = aug[pr], aug[r]
        inv = pow(aug[r][c], p - 2, p)
        aug[r] = [(v * inv) % p for v in aug[r]]
        for i in range(k):
            if i != r and aug[i][c] % p:
                f = aug[i][c]
                aug[i] = [(a - f * b) % p for a, b in zip(aug[i], aug[r])]
        piv_cols.append(c)
        r += 1
    free_cols = [c for c in range(k) if c not in piv_cols]
    basis = []
    for fc in free_cols:
        v = [0] * k
        v[fc] = 1
        for rr, pc in enumerate(piv_cols):
            v[pc] = (-aug[rr][fc]) % p
        basis.append(tuple(v))
    assert len(basis) == 2, f"kernel dim {len(basis)} != 2"
    b1, b2 = basis
    assert tuple((a + b) % p for a, b in zip(b1, frob2(b1))) == (0,) * k
    assert tuple((a + b) % p for a, b in zip(b2, frob2(b2))) == (0,) * k

    # For every kernel character a = c1 b1 + c2 b2: Tr(a x) = c1 al_x + c2 be_x.
    al = [tr_abs(K.mul(b1, x_)) for x_ in pts]
    be = [tr_abs(K.mul(b2, x_)) for x_ in pts]
    n_origin = sum(1 for a_, b_ in zip(al, be) if a_ == 0 and b_ == 0)
    log(f"  kernel characters kill mu_{n//2} pointwise: "
        f"{n_origin} of {n} elements have (Tr(b1 x), Tr(b2 x)) = (0,0) "
        f"(predicted {n//2})")

    grid = np.zeros((p, p), dtype=np.float64)
    for a_, b_ in zip(al, be):
        grid[a_, b_] += 1.0
    S = np.fft.fft2(grid)
    A = np.abs(S)
    A[0, 0] = -1.0
    Mker = float(A.max())
    lawb = math.sqrt(2 * n * math.log(m))
    guarantee = n / 2 - (n / 2) / (p * p - 1)
    log(f"  exact sup over the p^2-1 = {p*p-1} kernel characters: "
        f"M_ker = {Mker:.4f}")
    log(f"  theorem guarantee n/2 - (n/2)/(p^2-1) = {guarantee:.4f}  "
        f"(M_ker >= guarantee: {Mker >= guarantee - 1e-9})")
    log(f"  prize-law bound sqrt(2 n ln m) = {lawb:.4f}")
    log(f"  M_E >= M_ker = {Mker:.2f} {'>' if Mker > lawb else '<='} {lawb:.2f}"
        f"  ==> LAW {'VIOLATED at this generating instance' if Mker > lawb else 'not separated here'}"
        f"  (violation factor {Mker/lawb:.3f}x)")
    log("")
    return Mker > lawb


def main():
    log("probe_466_ff_halftrap.py -- W4 supplement: half-trap theorem census + n=256 violation")
    log("")
    ok1 = part_S1()
    viols = [part_S2(p) for p in (577, 1087, 2111)]
    log("=" * 78)
    log(f"SUMMARY: S1 census {'CONFIRMED' if ok1 else 'FAILED'}; "
        f"S2 law-violations at n=256, k=4: {sum(viols)}/3 primes")
    log("  => every deg-f >= 3 residue-ring model of the thin 2-power law is either")
    log("     degenerate (trace collapse, M = n) or provably law-violating (half-trap,")
    log("     M >= n/2); deg f = 3 is arithmetically impossible. The FF residue model")
    log("     collapses to F_p / the two k=2 classes -- no new provable territory.")
    log("=" * 78)
    with open("scripts/probes/_out_466_ff_halftrap.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
