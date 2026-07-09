#!/usr/bin/env python3
# sweep_A09_halo_carriers.py  —  A09 supplement: characterize the HALO CARRIERS.
#
# At n=16, w=6 the char-0 e_2=0 count is 0, yet over F_q the count RISES (defect>0).
# These RISE-events come from sets S with e_2(S) != 0 in char 0 but e_2(S) = 0 mod q.
# This script characterizes them as the halo-form defect carriers:
#   - alpha := e_2(S) as an element of Z[zeta_n]  (a sparse signed sum of n-th roots),
#   - the carrier condition is  q | N(alpha)  i.e. q divides the field-norm /
#     equivalently alpha(zeta) = 0 for the embedding zeta = primitive n-th root mod q.
#   We exhibit explicit alpha, its norm N(alpha)=Res(Phi_n, alpha-poly), and the primes q
#   that divide it (= exactly the primes where S becomes a halo carrier).
#
# This is the concrete realization of the "halo-form": high-order spurious vanishing
# sums of mu_n mod p.  alpha is the structured defect-carrier the prize wall lives on.

import itertools
from sympy import isprime, primitive_root, Poly, symbols, resultant, cyclotomic_poly, factorint

X = symbols('X')

def vec_e2_char0(A, n):
    """e_2(S) = sum_{i<j in A} zeta^{i+j}, reduced in Z[zeta]/(zeta^{n/2}+1) -> length-h int vec."""
    h = n // 2
    v = [0] * h
    L = list(A)
    for a in range(len(L)):
        for b in range(a + 1, len(L)):
            e = (L[a] + L[b]) % n
            if e < h:
                v[e] += 1
            else:
                v[e - h] -= 1
    return v

def vec_to_poly(v):
    return Poly(sum(c * X**i for i, c in enumerate(v)), X)

def field_norm(v, n):
    """N(alpha) = Res(Phi_n(X), alpha(X)).  alpha given in basis 1..X^{h-1}."""
    Phi = Poly(cyclotomic_poly(n, X), X)
    a = vec_to_poly(v)
    return int(resultant(Phi, a))

def zeta_modq(q, n):
    g = primitive_root(q)
    return pow(g, (q - 1) // n, q)

def eval_modq(v, z, q):
    acc = 0; zp = 1
    for vi in v:
        if vi:
            acc = (acc + vi * zp) % q
        zp = (zp * z) % q
    return acc % q

def main():
    n, w = 16, 6
    h = n // 2
    print(f"A09 HALO-CARRIER characterization: n={n}, w={w} (char-0 count = 0)")
    print("A halo carrier S: e_2(S) != 0 in char 0 but e_2(S) = 0 mod q.")
    print("alpha := e_2(S);  carrier <=> q | N(alpha) = Res(Phi_n, alpha).\n")

    # enumerate all sets with e_2 != 0 in char 0; group by alpha=e_2 vector (as carrier seed)
    seed_norms = {}   # alpha-vector(tuple) -> N(alpha)
    seed_count = {}
    for A in itertools.combinations(range(n), w):
        v = tuple(vec_e2_char0(A, n))
        if any(v):  # e_2 != 0 in char 0
            seed_count[v] = seed_count.get(v, 0) + 1

    # compute norms for the distinct alpha seeds; collect prime divisors
    print(f"#distinct nonzero e_2 vectors (alpha seeds) among w={w} sets: {len(seed_count)}")
    prime_to_seeds = {}
    norms_sample = []
    for v, cnt in seed_count.items():
        N = field_norm(list(v), n)
        seed_norms[v] = N
        if len(norms_sample) < 8:
            norms_sample.append((v, N, cnt))
        if N != 0:
            for q in factorint(abs(N)):
                if q % n == 1 and q > 2:
                    prime_to_seeds.setdefault(q, []).append((v, N, cnt))

    print("\nsample alpha seeds (e_2 vectors), their field norm N(alpha), multiplicity:")
    for v, N, cnt in norms_sample:
        print(f"  alpha(coeffs zeta^0..zeta^{h-1})={v}  N={N}  (#sets={cnt}  N factors={dict(factorint(abs(N))) if N else '0'})")

    # which primes q=1 mod n are divisors of some N(alpha) -> exactly the halo primes
    print("\nprimes q = 1 (mod n) dividing some N(alpha)  ==  the halo primes (carrier turns on):")
    halo_primes = sorted(prime_to_seeds.keys())
    for q in halo_primes[:20]:
        seeds = prime_to_seeds[q]
        tot = sum(c for _, _, c in seeds)
        print(f"  q={q:>7}:  #carrier-seeds={len(seeds):>3}  total carrier-sets={tot:>4}")

    # cross-check against the direct mod-q test for the smallest few halo primes
    print("\nCROSS-CHECK: direct mod-q e_2=0 test on halo primes (should match carrier counts):")
    for q in halo_primes[:6]:
        z = zeta_modq(q, n)
        direct = 0
        for A in itertools.combinations(range(n), w):
            v = vec_e2_char0(A, n)
            if any(v) and eval_modq(v, z, q) == 0:
                direct += 1
        pred = sum(c for _, _, c in prime_to_seeds[q])
        ok = "OK" if direct == pred else "MISMATCH"
        print(f"  q={q:>7}: direct halo-sets={direct:>4}  norm-predicted={pred:>4}  [{ok}]")

    # also: are there primes q=1 mod n with NO halo carriers (defect 0 from w=6)?
    print("\nprimes q=1 mod n in [n+1, 600] with NO halo carrier (N(alpha) never divisible):")
    clean = []
    m = 1
    while True:
        q = n * m + 1
        if q > 600:
            break
        if isprime(q) and q not in prime_to_seeds:
            clean.append(q)
        m += 1
    print(f"  {clean}")

if __name__ == "__main__":
    main()
